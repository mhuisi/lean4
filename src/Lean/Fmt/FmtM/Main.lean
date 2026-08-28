/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Environment
public import Lean.Fmt.FmtM.Error
import Lean.Fmt.FmtM.Basic
import Std.Data.HashMap.AdditionalOperations
import Lean.Fmt.FmtM.Comments
import Lean.Fmt.Core.Formatter
public import Lean.Data.Position
import Init.Data.String.Iter.Intercalate
public import Lean.Language.Lean.Types
public import Lean.Fmt.FmtM.LineInfo
public import Lean.Fmt.FmtM.Comments
public import Lean.Fmt.FmtM.Attribute
import Lean.Language.Lean
import Lean.Fmt.Util.Module
import Init.System.Platform
import Std.Sync.Channel
import Lean.Fmt.Util.RangeTree

namespace Lean.Fmt

def filterAlreadyFormattedComments
    {rendering : String.Slice}
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (syntaxToRenderedWhitespace : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice)) :
    Std.HashMap Syntax.Range (Array Comment) :=
  -- It would be nice to have a range index structure for this.
  let renderedWhitespaceSyntaxRanges := syntaxToRenderedWhitespace.keysArray
  let comments := comments.map fun _ cs =>
    cs.filter fun c =>
      ! renderedWhitespaceSyntaxRanges.any (·.includes c.originalWhitespaceRange)
  comments.filter fun _ cs => ! cs.isEmpty

/--
Associates all syntax ranges that have been tagged by `Fmt.fmt` with the portions of the rendered
string that a specific tagged sub-document has been rendered to.
Tagged syntax ranges that do not appear in the rendered string at all are removed.
-/
def connectTags
    {rendering : String.Slice}
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    (tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.Subslice)) :
    Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice × RangeKind) :=
  -- 1. All `TagId`s in `tagsToRendered` are contained in `syntaxToTags`.
  -- 2. Only `Syntax.Range`s that have been assigned by the document construction will appear in
  --   `syntaxToTags`. This includes `Syntax` subtrees for which `Fmt.fmt` has been called,
  --   as well as all tokens that appear in the constructed document for which `Fmt.text` has been
  --   called.
  -- 3. `TagId`s in `syntaxToTags` that are not used in the specific alternative chosen by the
  --   formatter do not appear in `tagsToRendered`.
  -- 4. Multiple `TagId`s are associated with the same `Syntax.Range` in `syntaxToTags` when
  --    `Fmt.fmt` is called for a `Syntax` subtree that contains another `Syntax` subtree of the
  --    same range for which `Fmt.fmt` has also been called.
  -- 5. Multiple `rendering.Subslice`s are associated with the same `TagId` in `tagsToRendered` when
  --    a sub-document is shared in multiple places in the same alternative,
  --    e.g. when a formatter yields the same document twice for the same token in the
  --    input `Syntax`.
  syntaxToTags.filterMap fun _ (tags, kind) => do
    let mut ranges := {}
    for tag in tags do
      if let some rendered := tagsToRendered.get? tag then
        ranges := ranges.insertMany rendered
    ranges := ranges.filter (! ·.toSlice.isEmpty)
    guard <| ! ranges.isEmpty
    return (ranges, kind)

def normalize (rendering : String) : String := Id.run do
  let lines := rendering.split '\n'
  let lines := lines.map (·.dropEndWhile ' ')
  let lines := lines.toArray.popWhile (String.Slice.isEmpty ·)
  let lines := lines.push ""
  return lines.iter.intercalateString "\n"

public structure tryInsertingComments.Result where
  doc : Doc FmtCost
  pendingComments : Array Comment

private def placement (c : Comment) : Comment.RenderedPlacementKind :=
  match c.kind, c.placement with
  | .lineComment, .onLineBeforeToken
  | .blockComment, .onLineBeforeToken =>
    .afterClosestPreviousNewline
  | .lineComment, .afterToken =>
    if c.content.size > 1 then
      .afterClosestPreviousNewline
    else
      .beforeClosestNextNewline
  | .blockComment, .afterToken =>
    if c.content.size > 1 then
      .afterClosestPreviousNewline
    else
      .afterToken

public structure tryInsertingComments.State where
  comments : Std.HashMap TagId (Syntax.Range × Array Comment)
  cache : Std.HashMap (PtrKey (Doc FmtCost)) tryInsertingComments.Result
  freshTagId : TagId
  syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind)

public def tryInsertingComments
    (doc : Doc FmtCost)
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (freshTagId : TagId)
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    : Doc FmtCost × Std.HashMap Syntax.Range (Array TagId × RangeKind) := Id.run do
  -- It would be nice to have a range index structure for this.
  let handledWhitespaceSyntaxRanges := syntaxToTags.filter (fun _ (_, kind) => kind matches .whitespace) |>.keysArray
  let comments := comments.map fun _ cs =>
    cs.filter fun c =>
      ! handledWhitespaceSyntaxRanges.any (·.includes c.originalWhitespaceRange)
  let comments := comments.filter fun _ cs => ! cs.isEmpty
  let mut comments' := ∅
  for ⟨range, comments⟩ in comments do
    let tags := findBestTags range comments
    for (tag, rangeForTag, commentsForTag) in tags do
      comments' := comments'.insert tag (rangeForTag, commentsForTag)
  let init := {
    comments := comments'
    cache := ∅
    freshTagId
    syntaxToTags
  }
  let mut (doc, s) := StateT.run (s := init) do
    let ⟨d, p⟩ ← go doc
    let d ← insertComments d p
    return d
  return (doc, s.syntaxToTags)
where
  findBestTags (range : Syntax.Range) (comments : Array Comment) : Array (TagId × Syntax.Range × Array Comment) := Id.run do
    if let some (tags, _) := syntaxToTags.get? range then
      return #[(tags[0]!, range, comments)]
    let syntaxToTagsByStart := syntaxToTags.toArray.qsort fun (a, _) (b, _) =>
      let ord := (Ord.compare a.start b.start)
        |>.then (Ord.compare a.bsize b.bsize)
      ord.isLT
    let syntaxToTagsByStop := syntaxToTags.toArray.qsort fun (a, _) (b, _) =>
      let ord := (Ord.compare a.stop b.stop)
        |>.then (Ord.compare b.bsize a.bsize)
      ord.isLT
    let (commentsWithPreviousRangeFallback, commentsWithNextRangeFallback) :=
      comments.partition fun c => c.content.size <= 1 && c.placement matches .afterToken
    let (_, rangeForPreviousRangeFallback, tagsForPreviousRangeFallback, _) :=
      binSearchRightmost syntaxToTagsByStop range.stop (·.1.stop) (· < ·) |>.get!
    let (_, rangeForNextRangeFallback, tagsForNextRangeFallback, _) :=
      binSearchLeftmost syntaxToTagsByStart range.start (·.1.start) (· < ·) |>.get!
    let mut r := #[]
    if ! commentsWithPreviousRangeFallback.isEmpty then
      r := r.push (tagsForPreviousRangeFallback[0]!, rangeForPreviousRangeFallback, commentsWithPreviousRangeFallback)
    if ! commentsWithNextRangeFallback.isEmpty then
      r := r.push (tagsForNextRangeFallback[0]!, rangeForNextRangeFallback, commentsWithNextRangeFallback)
    return r
  tag (doc : Doc FmtCost) (c : Comment) : StateM tryInsertingComments.State (Doc FmtCost) :=
    modifyGet fun s =>
      let (freshTagId, syntaxToTags, doc) :=
        TaggedDoc.taggedWithRange s.freshTagId s.syntaxToTags doc c.originalWhitespaceRange .whitespace
      (doc.doc, { s with freshTagId, syntaxToTags })
  renderingToDoc (r : Comment.Rendering) : Doc FmtCost :=
    let lines := r.rendered.split '\n' |>.map (Doc.text ·.toString) |>.toArray
    .aligned <| .joinUsing .hardNl lines
  insertComments (anchor : Doc FmtCost) (cs : Array Comment) : StateM tryInsertingComments.State (Doc FmtCost) := do
    let penalty := 999999 -- All failure fallbacks in the document should take priority.
    let mut result := anchor
    for c in cs.reverse do
      match placement c with
      | .afterClosestPreviousNewline =>
        let renderings := c.render
        let docs := renderings.map (Doc.initial <| renderingToDoc ·)
        let docs ← docs.mapM (tag · c)
        let doc := Doc.free <| .oneOf docs
        let doc := .aligned <| doc ++ .hardNl ++ result
        result := .oneOf #[
          doc,
          Doc.costing (DefaultCost.ofFailureFallbackPenalty penalty) result
        ]
      | .beforeClosestNextNewline =>
        let renderings := c.render.filter (! ·.isMultiLine)
        let docs := renderings.map (Doc.final <| renderingToDoc ·)
        let docs ← docs.mapM (tag · c)
        let doc := Doc.free <| .oneOf docs
        let doc := result ++ .text " " ++ doc
        result := .oneOf #[
          doc,
          Doc.costing (DefaultCost.ofFailureFallbackPenalty penalty) result
        ]
      | .afterToken =>
        let renderings := c.render.filter (! ·.isMultiLine)
        let afterLineDocs := renderings.map (Doc.final <| renderingToDoc ·)
        let afterLineDocs ← afterLineDocs.mapM (tag · c)
        let afterLineDoc := Doc.free <| .oneOf afterLineDocs
        let afterLineDoc := result ++ .text " " ++ afterLineDoc
        let afterTokenDocs := renderings.map (renderingToDoc ·)
        let afterTokenDocs ← afterTokenDocs.mapM (tag · c)
        let afterTokenDoc := .oneOf afterTokenDocs
        let afterTokenDoc := result ++ .text " " ++ afterTokenDoc
        result := .oneOf #[
          afterTokenDoc,
          afterLineDoc,
          Doc.costing (DefaultCost.ofOverflowFallbackPenalty penalty) result
        ]
    return result
  goMemoized (v : Doc FmtCost)
      : StateM tryInsertingComments.State tryInsertingComments.Result := do
    let cacheKey := unsafe PtrKey.ofKey v
    if let some r := (← get).cache.get? cacheKey then
      return r
    let r ← go v
    modify fun s => {
      s with
      cache := s.cache.insert cacheKey r
    }
    return r
  go (d : Doc FmtCost)
      : StateM tryInsertingComments.State tryInsertingComments.Result := do
    match d with
    | .tagged id d =>
      let ⟨d, p⟩ ← goMemoized d
      let tagged := .tagged id d
      let some (_, commentsForId) := (← get).comments.get? id
        | return ⟨tagged, p⟩
      return ⟨tagged, p ++ commentsForId⟩
    | .failure
    | .text _
    | .newline _ =>
      return ⟨d, #[]⟩
    | .unflattenable d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.unflattenable d, p⟩
    | .flattened d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.flattened d, p⟩
    | .indented n c d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.indented n c d, p⟩
    | .aligned d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.aligned d, p⟩
    | .unindented onlyNonCumulative d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.unindented onlyNonCumulative d, p⟩
    | .final d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.final d, p⟩
    | .initial d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.initial d, p⟩
    | .free d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.free d, p⟩
    | .guarded a d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.guarded a d, p⟩
    | .costing c d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.costing c d, p⟩
    | .either d1 d2 =>
      let ⟨d1, p1⟩ ← goMemoized d1
      let ⟨d2, p2⟩ ← goMemoized d2
      let pShared := p1.filter (p2.contains ·)
      let p1Unshared := p1.filter (! pShared.contains ·)
      let d1 ← insertComments d1 p1Unshared
      let p2Unshared := p2.filter (! pShared.contains ·)
      let d2 ← insertComments d2 p2Unshared
      return ⟨.either d1 d2, pShared⟩
    | .append d1 d2 =>
      let mut ⟨d1, p1⟩ ← goMemoized d1
      let (commentsBefore1, commentsAfter1) := p1.partition (placement · matches .afterClosestPreviousNewline)
      if ! d2.isAlwaysEmpty then
        d1 ← insertComments d1 commentsAfter1
      let mut ⟨d2, p2⟩ ← goMemoized d2
      let (commentsBefore2, commentsAfter2) := p2.partition (placement · matches .afterClosestPreviousNewline)
      if ! d1.isAlwaysEmpty then
        d2 ← insertComments d2 commentsBefore2
      p1 :=
        if ! d2.isAlwaysEmpty then
          commentsBefore1
        else
          p1
      p2 :=
        if ! d1.isAlwaysEmpty then
          commentsAfter2
        else
          p2
      return ⟨.append d1 d2, p1 ++ p2⟩

public def insertRemainingComments
    (rendering : String)
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    (tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.toSlice.Subslice) compare)
    (comments : Std.HashMap Syntax.Range (Array Comment))
    : String :=
  let syntaxToRendered := connectTags syntaxToTags tagsToRendered
  let (syntaxToRenderedNodes, syntaxToRenderedWhitespace) := syntaxToRendered.partition fun _ (_, kind) =>
    ! (kind matches .whitespace)
  let syntaxToRenderedNodes := syntaxToRenderedNodes.map fun _ (ranges, _) => ranges
  let syntaxToRenderedWhitespace := syntaxToRenderedWhitespace.map fun _ (ranges, _) => ranges
  let comments := filterAlreadyFormattedComments comments syntaxToRenderedWhitespace
  insertComments 100 rendering syntaxToRenderedNodes comments

private structure CommandOutput where
  rendering : String
  syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind)
  tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.toSlice.Subslice) compare

def render (ctx : Fmt.Context) (stx : Syntax) (act : FmtM TaggedDoc) : Except Error CommandOutput := do
  let r ← FmtM.run ctx act
  let doc := r.value.doc
  let output ← format? 100 200 doc (taintedResolution := false)
    |>.mapError (Error.ofFormattingError stx)
  return ⟨output.rendering, r.tags, output.tags⟩

def commandRaw (ctx : Fmt.Context) (stx : Syntax) : Except Error String := do
  let some fullSyntaxRange := stx.getRange?
    | throw <| .malformedInputSyntax stx none "Missing range"
  let some start := ctx.text.source.pos? fullSyntaxRange.start
    | throw <| .malformedInputSyntax stx none "Invalid range"
  let some stop := ctx.text.source.pos? fullSyntaxRange.stop
    | throw <| .malformedInputSyntax stx none "Invalid range"
  let leading := (← render ctx stx <| fmtLeadingWithRetainedNewlinesAndComments stx).rendering
  let rawText := ctx.text.source.extract start stop
  let trailing := (← render ctx stx <| fmtTrailingWithRetainedNewlinesAndComments stx).rendering
  return leading ++ rawText ++ trailing

public def commandMain (ctx : Fmt.Context) (stx : Syntax) : Except Error String := do
  let comments ← collectComments ctx.lineInfos stx
  try
    let r ← FmtM.run ctx do
      let leading ← fmtLeadingWithRetainedNewlinesAndComments stx
      let doc ← fmt stx
      let trailing ← fmtTrailingWithRetainedNewlinesAndComments stx
      return leading ++ doc ++ trailing
    let doc := r.value.doc
    let syntaxToTags := r.tags
    let (doc, syntaxToTags) := tryInsertingComments doc comments r.freshTagId syntaxToTags
    let output ← format? 100 200 doc (taintedResolution := false)
      |>.mapError (Error.ofFormattingError stx)
    let tagsToRendered := output.tags
    let rendering := insertRemainingComments output.rendering syntaxToTags tagsToRendered comments
    return rendering
  catch _ =>
    commandRaw ctx stx

def getNumThreads : BaseIO Nat := do
  if ! System.Platform.isEmscripten then
    if let some s ← IO.getEnv "LEAN_NUM_THREADS" then
      return s.trimAscii.toNat?.getD 0
  return (System.Platform.Internal.getHardwareConcurrency ()).toNat

def getParallelism : BaseIO Nat :=
  return max 1 (← getNumThreads)

public def fileMain (initialSnap : Language.Lean.InitialSnapshot) : BaseIO (Except Error String) := do
  run
where
  run : ExceptT Error BaseIO String := do
    let text := initialSnap.ictx.fileMap
    let some finalCmdState := Language.Lean.waitForFinalCmdState? initialSnap
      | throw <| .headerError initialSnap.stx
    let moduleData := Language.Lean.moduleData initialSnap |>.get
    if moduleData.hasParseErrors then
      throw .parseError
    let headerStx := moduleData.headerData.stx
    let cmdStxs := moduleData.cmdData.map (·.stx)
    let some modStx := mkModuleSyntax? headerStx cmdStxs
      | throw .earlyTerminationCommand
    let (some headerCmdState, some headerParserState) :=
        (moduleData.headerData.cmdState?, moduleData.headerData.parserState?)
      | throw <| .headerError headerStx
    let allCmdData : Array Language.Lean.CommandData := #[⟨headerStx, headerParserState, headerCmdState⟩] ++ moduleData.cmdData
    -- TODO: Use `collectSyntaxLineInfos` again once Verso docstrings are fixed and no longer
    -- produce tokens without source positions.
    let lineInfos := collectSyntaxLineInfos' text.source.toSlice modStx
    let ctx : Fmt.Context := {
      lineInfos
      env := finalCmdState.env
      text
      initialSnap? := some initialSnap
      opts := finalCmdState.scopes[0]!.opts
    }
    let renderedHeader ← commandMain ctx headerStx
    let parallelism ← getParallelism
    let renderedCommandsMutex : Std.Mutex (Std.TreeMap Nat (Except Error String)) ← Std.Mutex.new ∅
    let jobs : Std.Channel Nat ← Std.Channel.new
    for cmdIdx in (1...allCmdData.size) do
      IO.wait (α := Unit) <| ← jobs.send cmdIdx
    let mut tasks := #[]
    for _ in (0...Nat.min parallelism (allCmdData.size - 1)) do
      let t ← BaseIO.asTask (prio := .dedicated) do
        while true do
          let some cmdIdx ← jobs.tryRecv
            | return
          let some cmdData := allCmdData[cmdIdx]?
            | unreachable!
          let some prevCmdData := allCmdData[cmdIdx-1]?
            | unreachable!
          let rendered? := renderCommand ctx cmdData prevCmdData
          renderedCommandsMutex.atomically do
            modify (·.insert cmdIdx rendered?)
      tasks := tasks.push t
    for task in tasks do
      IO.wait (α := PUnit) task
    let renderedCommands : Array String ← (← renderedCommandsMutex.atomically get).valuesArray.mapM fun (renderedCommand? : Except Error String) =>
      renderedCommand?
    let renderedFile := renderedHeader ++ renderedCommands.iter.joinString
    return normalize renderedFile
  renderCommand (ctx : Context) (cmdData prevCmdData : Language.Lean.CommandData) : Except Error String := do
    let input := initialSnap.ictx.inputString
    let mut renderedCommand ← commandMain ctx cmdData.stx
    let (some startPos, some endPos) := (cmdData.stx.getStartPos? >>= String.pos? input, cmdData.stx.getTrailingTailPos? >>= String.pos? input)
      | return renderedCommand
    let inputWithRenderedCommand := input.extract input.startPos startPos ++ renderedCommand ++ input.extract endPos input.endPos
    let ictx := Parser.InputContext.mk inputWithRenderedCommand initialSnap.ictx.fileName
    let pmctx := {
      env := prevCmdData.cmdState.env
      options := prevCmdData.cmdState.scopes[0]!.opts
      currNamespace := prevCmdData.cmdState.scopes[0]!.currNamespace
      openDecls := prevCmdData.cmdState.scopes[0]!.openDecls
    }
    let (stx, _, msgLog) := Parser.parseCommand ictx pmctx prevCmdData.parserState MessageLog.empty
    if msgLog.hasErrors || stx.hasMissing then
      renderedCommand ← commandRaw ctx cmdData.stx
    return renderedCommand
