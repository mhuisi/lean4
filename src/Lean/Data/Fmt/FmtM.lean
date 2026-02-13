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

namespace Lean

public structure Fmt.Context where
  env : Environment

public structure Fmt.State where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  tags : Std.HashMap TagId Syntax.Range

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
    Except Fmt.Error (α × Std.HashMap Fmt.TagId Syntax.Range) := do
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
      tags := s.tags.insertIfNew currentTagId range
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

structure Comment where
  kind : Comment.Kind
  placement : Comment.Placement
  full : String
  content : String

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
    content
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
          content := ""
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

def rangeCompare (a b : Syntax.Range) : Ordering :=
  Ord.compare a.start.byteIdx b.start.byteIdx
    |>.then (Ord.compare a.stop.byteIdx b.stop.byteIdx)

structure reassociateComments.State where
  cache : Std.HashMap USize (Std.TreeMap Syntax.Range (Std.HashSet TagId) rangeCompare)

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

def reassociateComments
    (doc : Fmt.Doc)
    (tags : Std.HashMap TagId Syntax.Range)
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    Std.HashMap TagId (Array Comment) := Id.run do
  let r ← StateT.run' (goMemoized doc) { cache := {} : reassociateComments.State }
  let mut r' := ∅
  for (commentRange, ids) in r do
    let comments := comments.get! commentRange
    for id in ids do
      r' := r'.alter id fun
        | none =>
          some comments
        | some existingComments =>
          -- `r` is sorted by the ranges of the tokens that comments are attached to,
          -- so when multiple sets of comments get associated with the same `id`,
          -- they will be ordered according to the ranges of the tokens they are attached to.
          -- This maintains the relative order of comments in the input syntax.
          some <| existingComments ++ comments
  return r'
where
  goMemoized (doc : Fmt.Doc) :
      StateT reassociateComments.State Id
        (Std.TreeMap Syntax.Range (Std.HashSet TagId) rangeCompare) := do
    let cacheKey := unsafe ptrAddrUnsafe doc
    if let some cached := (← get).cache.get? cacheKey then
      return cached
    let r ← go doc
    modify fun s => { s with cache := s.cache.insert cacheKey r }
    return r
  go (doc : Fmt.Doc) :
      StateT reassociateComments.State Id
        (Std.TreeMap Syntax.Range (Std.HashSet TagId) rangeCompare) := do
    match doc with
    | .tagged id d =>
      let associatedComments1 ← goMemoized d
      let associatedComments2 := getAssociatedComments id
      -- If a set of comments has already been assigned in `d`, use those.
      return associatedComments2.insertMany associatedComments1
    | .failure
    | .newline ..
    | .text .. =>
      return ∅
    | .flattened d
    | .indented _ _ d
    | .aligned d
    | .full d
    | .unindented d =>
      goMemoized d
    | .append a b =>
      let associatedComments1 ← goMemoized a
      let associatedComments2 ← goMemoized b
      -- If a set of comments has already been assigned in `a`, prefer those over ones from `b`.
      return associatedComments2.insertMany associatedComments1
    | .either a b =>
      let associatedComments1 ← goMemoized a
      let associatedComments2 ← goMemoized b
      -- Comments must always be assigned in all alternatives.
      -- If a comment is assigned in just one of the alternatives, then assigning it again
      -- above the `either` may duplicate the comment, whereas not assigning it at all will erase
      -- the comment if the alternative where the comment isn't assigned is chosen by the formatter.
      return interWith associatedComments1 associatedComments2 fun _ tags1 tags2 =>
        tags1.union tags2
  getAssociatedComments (id : TagId) : Std.TreeMap Syntax.Range (Std.HashSet TagId) rangeCompare :=
    let refRange := tags.get! id
    -- TODO: Assumes that we have an exact range match for every comment
    -- Use all comments that match refRange here?
    comments.get? refRange
      |>.map (fun _ => Std.TreeMap.ofArray (cmp := rangeCompare) #[(refRange, { id })])
      |>.getD ∅

public def main (env : Environment) (stx : Syntax) : Except Error String := do
  let comments ← collectComments stx
  let (taggedDoc, tags) ← FmtM.run env <| fmt stx
  let doc := taggedDoc.doc
  let some output := format? doc 80
    | throw <| .formattingFailure stx doc
  return output.rendering
