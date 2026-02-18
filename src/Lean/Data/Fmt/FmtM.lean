/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Formatter
public import Lean.KeyedDeclsAttribute
import Lean.Parser.Extension
import Lean.ExtraModUses
import Lean.Elab.InfoTree.Main
public import Lean.Util.ShareCommon
import Std.Data.HashMap.AdditionalOperations
import Std.Data.HashMap.Iterator
import Std.Data.Iterators.Producers.Slice

def Array.binSearchRightmost (xs : Array α) (query : β) (key : α → β) (lt : β → β → Bool) : Option (Nat × α) := do
  let mut l := 0
  let mut r := xs.size
  while l < r do
    let m := l + (r - l) / 2
    let some v := xs[m]?
      | unreachable!
    if lt query (key v) then
      r := m
    else
      l := m + 1
  let i := r - 1
  let v ← xs[i]?
  guard <| !(lt query (key v)) -- key v <= query
  return (i, v)

def Array.binSearchLeftmost (xs : Array α) (query : β) (key : α → β) (lt : β → β → Bool) : Option (Nat × α) := do
  let mut l := 0
  let mut r := xs.size
  while l < r do
    let m := l + (r - l) / 2
    let some v := xs[m]?
      | unreachable!
    if lt (key v) query then
      l := m + 1
    else
      r := m
  let i := l
  let v ← xs[i]?
  guard <| !(lt (key v) query) -- query <= key v
  return (i, v)

def String.indent (s : String) (numSpaces : Nat) : String :=
  s.split "\n"
    |>.map (fun line => "".pushn ' ' numSpaces ++ line.toString)
    |>.toList
    |> "\n".intercalate

namespace Lean

public structure Fmt.Context where
  env : Environment

public structure Fmt.State where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  tags : Std.HashMap Syntax.Range (Array TagId)

public structure Fmt.TaggedDoc where
  doc : Fmt.Doc

public inductive Fmt.Error where
  | partialFormatter
    (kind : SyntaxNodeKind)
    (msg : String := s!"Formatter for syntax kind `{kind}` is partial and does not handle the full \
      syntax of `{kind}`.")
  | formattingFailure
    (stx : Syntax)
    (doc : Doc)
    (msg : String := "Formatting of the document produced by the current set of `[fmt]` \
      annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to \
      flatten a document with hard newlines.")
  | malformedInputSyntax
    (stx : Syntax)
    (malformedPortion : Substring.Raw)
    (reason : String)
    (msg : String := s!"Input syntax to the formatter is malformed: {reason}. Offending portion \
      of the input syntax: {malformedPortion.toString}")
  | raw
    (msg : String)
  deriving Inhabited

public abbrev FmtM α := ReaderT Fmt.Context (ExceptT Fmt.Error (StateT Fmt.State Id)) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

public def FmtM.run (env : Environment) (act : FmtM α) :
    Except Fmt.Error (α × Std.HashMap Syntax.Range (Array Fmt.TagId )) := do
  let (v?, s) := ReaderT.run act { env }
    |>.run { shareCommonState := default, freshTagId := Nat.zero, tags := ∅ }
  return (← v?, s.tags)

instance : MonadShareCommon FmtM where
  withShareCommon v _ := modifyGet fun s =>
    let (v, shareCommonState) := s.shareCommonState.shareCommon v
    (v, { s with shareCommonState })

namespace Fmt

public def throwPartialFormatter : FmtM α :=
  throw <| .partialFormatter .anonymous

public def untagged (doc : Fmt.Doc) : TaggedDoc :=
  ⟨doc⟩

public def tagged (doc : Fmt.Doc) (ref : Syntax) : FmtM TaggedDoc := do
  let some range := ref.getRange?
    | return ⟨doc⟩
  modify fun s =>
    let currentTagId : Nat := s.freshTagId
    { s with
      freshTagId := currentTagId + 1
      tags := s.tags.alter range fun
        | none => some #[currentTagId]
        | some tags => some <| tags.push currentTagId

    }
  return ⟨doc⟩

public def TaggedDoc.isTagged (d : TaggedDoc) : Bool :=
  d.doc matches .tagged ..

public def TaggedDoc.tag (d : TaggedDoc) (ref : Syntax) : FmtM TaggedDoc := do
  if d.isTagged then
    return d
  tagged d.doc ref

public def failure : TaggedDoc :=
  untagged .failure
public def newline (flattened? : Option String) : TaggedDoc :=
  untagged (.newline flattened?)
public def nl : TaggedDoc :=
  untagged .nl
public def «break» : TaggedDoc :=
  untagged .break
public def hardNl : TaggedDoc :=
  untagged .hardNl
public def text (s : String) (ref : Syntax) : FmtM TaggedDoc :=
  tagged (.text s) ref
public def space : TaggedDoc :=
  untagged (.text " ")
public def nested (d : TaggedDoc) : TaggedDoc :=
  untagged <| .nested d.doc
public def hardNested (d : TaggedDoc) : TaggedDoc :=
  untagged <| .hardNested d.doc
public def flattened (d : TaggedDoc) : TaggedDoc :=
  untagged <| .flattened d.doc
public def maybeFlattened (d : TaggedDoc) : TaggedDoc :=
  untagged <| .maybeFlattened d.doc
public def unindented (d : TaggedDoc) : TaggedDoc :=
  untagged <| .unindented d.doc
public def full (d : TaggedDoc) : TaggedDoc :=
  untagged <| .full d.doc
public def either (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .either a.doc b.doc
public def append (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .append a.doc b.doc
public def join (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .join <| ds.map (·.doc)

public instance : Append TaggedDoc where
  append := append

unsafe builtin_initialize fmtAttribute : KeyedDeclsAttribute Fmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_fmt,
    name := `fmt,
    descr := "Register an Fmt formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      if ! (builtin && (env.find? id).isSome || Parser.isValidSyntaxNodeKind env id) then
        throwError "Invalid `[fmt]` argument: Unknown syntax kind `{id}`"
      if (← getEnv).contains id then
        recordExtraModUseFromDecl (isMeta := false) id
        if (← Elab.getInfoState).enabled then
          Elab.addConstInfo stx id none
      pure id
  }

public def fmt : Fmt := fun stx => match stx with
  | .missing =>
    pure <| failure
  | .atom _ val =>
    text val stx
  | .ident _ _ val _ =>
    text val.toString stx
  | .node .. => do
    let ctx ← read
    let kind := stx.getKind
    let fmts := fmtAttribute.getValues ctx.env kind
    let some f := fmts.head?
      | panic! s!"No formatter found for kind '{kind}' of the following syntax: {stx}"
    let r ← f stx
    try
      let r ← r.tag stx
      withShareCommon r
    catch e =>
      if let .partialFormatter errorKind _ := e then
        if errorKind == .anonymous then
          throw <| .partialFormatter kind
      throw e

inductive Comment.Placement where
  | afterToken
  | onLineBeforeToken

inductive Comment.Kind where
  | lineComment
  | blockComment

def Comment.Kind.startSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "--"
  | .blockComment => "/-"

def Comment.Kind.endSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "\n"
  | .blockComment => "-/"

def Comment.Kind.hasNesting (kind : Comment.Kind) : Bool :=
  match kind with
  | .lineComment => false
  | .blockComment => true

inductive Comment.RenderedPlacement where
  | afterClosestPreviousNewline
  | beforeClosestNextNewline
  | afterToken

structure Comment where
  kind : Comment.Kind
  placement : Comment.Placement
  full : String
  content : Array String

def Comment.toString (c : Comment) : String :=
  match c.kind with
  | .lineComment =>
    c.content.map (s!"-- {·}") |>.toList |> "\n".intercalate
  | .blockComment =>
    if c.content.size == 1 then
      s!"/- {c.content[0]!} -/"
    else
      s!"/-\n{"\n".intercalate c.content.toList}\n-/"

def Comment.renderedPlacements (c : Comment) : Array RenderedPlacement :=
  let isMultiLine := c.content.size > 1
  match c.kind, c.placement with
  | .lineComment, .afterToken =>
    if isMultiLine then
      #[.afterClosestPreviousNewline]
    else
      #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
  | .lineComment, .onLineBeforeToken =>
    #[.afterClosestPreviousNewline]
  | .blockComment, .afterToken =>
    if isMultiLine then
      #[.afterClosestPreviousNewline]
    else
      #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
  | .blockComment, .onLineBeforeToken =>
    #[.afterClosestPreviousNewline]

structure PendingComment extends Comment where
  startColumnOffset : Nat
  startPos : String.Pos.Raw

def PendingComment.finalize (p : PendingComment) : Comment :=
  let s := p.full.toSlice.dropPrefix p.kind.startSymbol
    |>.dropSuffix p.kind.endSymbol
  let lines := s.split "\n" |>.toArray
  let deindentedLines :=
    lines[0]! :: lines[1:].toList.map (dropIndentation · p.startColumnOffset)
  let deindentedLines := deindentedLines.map (·.toString)
  let content := "\n".intercalate deindentedLines
    |>.toSlice
    |> normalizeContent p.kind
    |>.toString
  {
    kind := p.kind
    placement := p.placement
    full := p.full
    content := content.split "\n" |>.toArray.map (·.toString)
  }
where
  normalizeContent (kind : Comment.Kind) (s : String.Slice) : String.Slice :=
    match kind with
    | .lineComment =>
      s.dropPrefix " " |>.dropSuffix "\n"
    | .blockComment =>
      s.dropPrefix " "
        |>.dropPrefix "\n"
        |>.dropSuffix "\n"
        |>.dropSuffix " "
  dropIndentation (line : String.Slice) (amount : Nat) : String.Slice := Id.run do
    let mut line := line
    let mut amount := amount
    while ! line.isEmpty && amount > 0 do
      let c := line.front
      if c != ' ' then
        break
      line := line.drop 1
      amount := amount - 1
    return line

def advanceColumnOffset (columnOffset : Nat) (s : String.Slice) : Nat :=
  match s.revFind? '\n' with
  | none =>
    columnOffset + s.positions.length
  | some nlPos =>
    s.sliceFrom nlPos.next! |>.positions.length

def parseComments (trailingWs : String.Slice) (columnOffset : Nat) : Array Comment × Nat := Id.run do
  let kinds := #[Comment.Kind.lineComment, Comment.Kind.blockComment]

  let firstNewlinePos := trailingWs.find '\n' |>.str

  let mut trailingWs := trailingWs
  let mut columnOffset : Nat := columnOffset
  let mut comments : Array PendingComment := #[]

  let mut commentNestingLevel : Nat := 0
  let mut pendingComment? : Option PendingComment := none

  while ! trailingWs.isEmpty do
    match pendingComment? with
    | none =>
      let currentPos := trailingWs.startPos.str.offset
      let isAfterNewline := currentPos >= firstNewlinePos.offset
      let startMatch? := kinds.findSome? fun kind => do
        return (kind, ← trailingWs.dropPrefix? kind.startSymbol)
      if let some (kind, trailingWs') := startMatch? then
        pendingComment? := some {
          kind := kind
          placement := if isAfterNewline then .onLineBeforeToken else .afterToken
          full := kind.startSymbol
          content := #[]
          startColumnOffset := columnOffset
          startPos := currentPos
        }
        commentNestingLevel := 1
        trailingWs := trailingWs'
        columnOffset := advanceColumnOffset columnOffset kind.startSymbol
        continue
      let c := trailingWs.front
      trailingWs := trailingWs.drop 1
      columnOffset := advanceColumnOffset columnOffset c.toString
      continue
    | some pendingComment =>
      let kind := pendingComment.kind
      let endMatch? := trailingWs.dropPrefix? kind.endSymbol
      if let some trailingWs' := endMatch? then
        commentNestingLevel := commentNestingLevel - 1
        let pendingComment := { pendingComment with
          full := pendingComment.full ++ kind.endSymbol
        }
        if !kind.hasNesting || commentNestingLevel == 0 then
          comments := comments.push pendingComment
          pendingComment? := none
        else
          pendingComment? := some pendingComment
        trailingWs := trailingWs'
        columnOffset := advanceColumnOffset columnOffset kind.endSymbol
        continue
      if kind.hasNesting then
        let startMatch? := trailingWs.dropPrefix? kind.startSymbol
        if let some trailingWs' := startMatch? then
          commentNestingLevel := commentNestingLevel + 1
          pendingComment? := some { pendingComment with
            full := pendingComment.full ++ kind.startSymbol
          }
          trailingWs := trailingWs'
          columnOffset := advanceColumnOffset columnOffset kind.startSymbol
          continue
      let c := trailingWs.front
      pendingComment? := some { pendingComment with
        full := pendingComment.full.push c
      }
      trailingWs := trailingWs.drop 1
      columnOffset := advanceColumnOffset columnOffset c.toString
      continue
  if let some pendingComment := pendingComment? then
    if pendingComment.kind.endSymbol.all Char.isWhitespace then
      comments := comments.push pendingComment
      pendingComment? := none
  let finalized := comments.map (·.finalize)
  return (finalized, columnOffset)

structure collectComments.State where
  pendingComments : Array Comment := #[]
  comments : Std.HashMap Syntax.Range (Array Comment) := {}
  columnOffset : Nat := 0 -- TODO: init?

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

def collectComments (stx : Syntax) :
    Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let (_, s) ← StateT.run (s := { : collectComments.State }) <| go stx
  return s.comments
where
  go (stx : Syntax) : collectComments.M Unit := do
    match stx with
    | .missing =>
      return
    | .atom info val =>
      collectTokenComments info val
    | .ident info rawVal .. =>
      let rawVal ← toSlice rawVal
      collectTokenComments info rawVal
    | .node _ _ args =>
      for arg in args do
        go arg
  collectTokenComments (info : SourceInfo) (tk : String.Slice) : collectComments.M Unit := do
    let some range := info.getRange?
      | throw <| .malformedInputSyntax stx (.ofSlice tk) "missing token range"
    let pendingComments ← modifyGet fun s =>
      (s.pendingComments, { s with pendingComments := #[] })
    addComments range pendingComments
    advanceColumnOffset tk
    let some trailing ← getTrailing? info
      | return
    let (comments, columnOffset) := parseComments trailing (← get).columnOffset
    let (commentsAfterToken, commentsOnLineBeforeToken) :=
      comments.partition (·.placement matches .afterToken)
    addComments range commentsAfterToken
    modify fun s => { s with
      pendingComments := s.pendingComments ++ commentsOnLineBeforeToken
      columnOffset
    }
    advanceColumnOffset trailing
  addComments (range : Syntax.Range) (newComments : Array Comment) : collectComments.M Unit := do
    modify fun s => { s with
      comments := s.comments.alter range fun
        | none => some newComments
        | some comments => some <| comments ++ newComments
    }
  advanceColumnOffset (val : String.Slice) : collectComments.M Unit :=
    modify fun s => { s with
      columnOffset := Fmt.advanceColumnOffset s.columnOffset val
    }
  toSlice (s : Substring.Raw) : collectComments.M String.Slice := do
    let some s := s.toSlice?
      | throw <| .malformedInputSyntax stx s
          "substring is invalid and cannot be converted to a slice"
    return s
  getTrailing? (info : SourceInfo) : collectComments.M (Option String.Slice) := do
    let some trailing := info.getTrailing?
      | return none
    toSlice trailing

def interWith (t₁ t₂ : Std.TreeMap α β cmp) (mergeFn : α → β → β → β) :
    Std.TreeMap α β cmp := Id.run do
  let (t₁, t₂) :=
    if t₁.size <= t₂.size then
      (t₁, t₂)
    else
      (t₂, t₁)
  let mut r := ∅
  for (k₁, v₁) in t₁ do
    let some v₂ := t₂.get? k₁
      | continue
    let v := mergeFn k₁ v₁ v₂
    r := r.insert k₁ v
  return r

structure RangeTreeNode (α : Type) where
  range : Syntax.Range
  value : α
  children : Array (RangeTreeNode α)
  deriving Inhabited, Repr

structure RangeTree (α : Type) where
  roots : Array (RangeTreeNode α)
  deriving Inhabited, Repr

def compareRangesLargest (a b : Syntax.Range) : Ordering :=
  Ord.compare a.start.byteIdx b.start.byteIdx
    |>.then (Ord.compare b.stop.byteIdx a.stop.byteIdx)

def compareRangesSmallest (a b : Syntax.Range) : Ordering :=
  Ord.compare a.start.byteIdx b.start.byteIdx
    |>.then (Ord.compare a.stop.byteIdx b.stop.byteIdx)

partial def RangeTree.ofHashMap [Inhabited α] (entries : Std.HashMap Syntax.Range α) : RangeTree α := Id.run do
  let entries := entries.toArray.qsort (fun (a, _) (b, _) => compareRangesLargest a b == .lt)
  let mut roots := #[]
  let mut i := 0
  while true do
    let (i', some root) := go entries i
      | break
    i := i'
    roots := roots.push root
  return ⟨roots⟩
where
  go (entries : Array (Syntax.Range × α)) (i : Nat) : Nat × Option (RangeTreeNode α) := Id.run do
    let some (range, value) := entries[i]?
      | (i, none)
    let mut children : Array (RangeTreeNode α) := #[]
    let mut i := i + 1
    while entries[i]?.any (fun (childRange, _) => range.includes childRange) do
      let (i', childNode?) := go entries i
      i := i'
      if let some childNode := childNode? then
        children := children.push childNode
    return (i, some ⟨range, value, children⟩)

partial def RangeTree.findSmallestRangeContaining? [Inhabited α] (t : RangeTree α) (range : Syntax.Range) :
    Option (Syntax.Range × α) := do
  let child ← findChildContaining t.roots range
  go child
where
  go (t : RangeTreeNode α) : Option (Syntax.Range × α) := do
    guard <| t.range.includes range
    let some child := findChildContaining t.children range
      | return (t.range, t.value)
    let some childMatch := go child
      | return (t.range, t.value)
    return childMatch
  findChildContaining (children : Array (RangeTreeNode α)) (range : Syntax.Range) : Option (RangeTreeNode α) :=
    children.binSearchRightmost range (·.range) (·.start < ·.start) |>.map (·.2)

def connectTags
    {rendering : String}
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId))
    (tagsToRendered : Std.HashMap TagId (Array (String.Slice.Subslice rendering))) :
    Std.HashMap Syntax.Range (Array (String.Slice.Subslice rendering)) :=
  -- Invariants:
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
  -- 5. Multiple `String.Slice`s are associated with the same `TagId` in `tagsToRendered` when
  --    a sub-document is shared in multiple places in the same alternative,
  --    e.g. when a formatter yields the same document twice for the same token in the
  --    input `Syntax`.
  syntaxToTags.map fun _ tags =>
    tags.flatMap fun tag =>
      tagsToRendered.getD tag #[]

def reassociateComments
    {rendering : String}
    (syntaxToRendered : Std.HashMap Syntax.Range (Array (String.Slice.Subslice rendering)))
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    Std.HashMap (String.Slice.Subslice rendering) (Array Comment) := Id.run do
  let syntaxToRendered := RangeTree.ofHashMap syntaxToRendered
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => compareRangesSmallest a b == .lt)
  let mut r : Std.HashMap (String.Slice.Subslice rendering) (Array Comment) := ∅
  for (commentRange, comments) in comments do
    let (_, ranges) := syntaxToRendered.findSmallestRangeContaining? commentRange |>.get!
    r := r.alter ranges[0]! fun
      | none => some comments
      | some previousComments => some <| previousComments ++ comments
  return r

structure LineInfo (s : String.Slice) where
  length : Nat
  indentation : Nat
  range : s.Subslice
  deriving Inhabited

def collectLineInfos (s : String.Slice) : Array (LineInfo s) := Id.run do
  let mut r := #[]
  let mut lineLength : Nat := 0
  let mut lineIndentation : Nat := 0
  let mut foundNonSpaceChar : Bool := false
  let mut lineStartPos := s.startPos
  let mut pos := s.startPos
  while h : pos ≠ s.endPos do
    let c := pos.get h
    let pos' := pos.next h
    if c == ' ' && ! foundNonSpaceChar then
      lineLength := lineLength + 1
      lineIndentation := lineIndentation + 1
    else if c == '\n' then
      r := r.push {
        length := lineLength
        indentation := lineIndentation
        range := s.subslice! lineStartPos pos
      }
      lineLength := 0
      lineIndentation := 0
      lineStartPos := pos'
      foundNonSpaceChar := false
    else
      lineLength := lineLength + 1
      foundNonSpaceChar := true
    pos := pos'
  r := r.push {
    length := lineLength
    indentation := lineIndentation
    range := s.subslice! lineStartPos pos
  }
  return r

def insertComments
    (maxColumnWidth : Nat)
    (rendering : String.Slice)
    (comments : Std.HashMap (String.Slice.Subslice rendering) (Array Comment)) :
    String :=
  let lineInfos := collectLineInfos rendering
  sorry
where
  determineInsertions
      (range : String.Slice.Subslice rendering)
      (comments : Array Comment)
      (lineInfos : Array (LineInfo rendering)) :
      Array (rendering.Pos × String) := Id.run do
    -- TODO:
    -- - multiple insertions at the same position
    -- - max line length handling on multiple insertions in the same line (solution: allow only 1)
    -- - sort the result so that we can compute the result
    let mut r := #[]
    for c in comments do
      let rps := c.renderedPlacements
      for rp in rps do
        match rp with
        | .afterClosestPreviousNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.startInclusive
          let insertionPos := lineInfo.range.startInclusive
          let insertedComment := c.toString.indent lineInfo.indentation ++ "\n"
          r := r.push (insertionPos, insertedComment)
        | .beforeClosestNextNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          let insertionPos := lineInfo.range.endExclusive
          let insertedComment := " " ++ c.toString
          let newLineLength := lineInfo.length + insertedComment.length
          if newLineLength > maxColumnWidth then
            continue
          r := r.push (insertionPos, insertedComment)
        | .afterToken =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          let insertionPos := range.endExclusive
          let insertedComment := " " ++ c.toString ++ " "
          let newLineLength := lineInfo.length + insertedComment.length
          if newLineLength > maxColumnWidth then
            continue
          r := r.push (insertionPos, insertedComment)
    return r
  findLineInfoContaining (lineInfos : Array (LineInfo rendering)) (pos : rendering.Pos) : Nat × LineInfo rendering :=
    lineInfos.binSearchRightmost pos (·.range.startInclusive) (· < ·) |>.get!

public def main (env : Environment) (stx : Syntax) : Except Error String := do
  let comments ← collectComments stx
  let (taggedDoc, syntaxToTags) ← FmtM.run env <| fmt stx
  let doc := taggedDoc.doc
  let some output := format? doc 80
    | throw <| .formattingFailure stx doc
  let tagsToRendered := output.tags
  let syntaxToRendered := connectTags syntaxToTags tagsToRendered
  let comments := reassociateComments syntaxToRendered comments
  let rendering := insertComments output.rendering comments
  return rendering
