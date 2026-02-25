/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Formatter
public import Lean.KeyedDeclsAttribute
public import Lean.Util.ShareCommon
public import Lean.Data.Fmt.Comments
import Lean.Parser.Extension
import Lean.ExtraModUses
import Lean.Elab.InfoTree.Main
import Std.Data.HashMap.AdditionalOperations
import Lean.Data.Fmt.RangeTree
import Std.Data.Iterators.Producers.Array
import Std.Data.Iterators.Producers.Empty
import Std.Data.HashSet.Iterator
public import Lean.Data.Fmt.LineInfo

def String.deindent (s : String) (numSpaces : Nat) : String :=
  s.split "\n"
    |>.map (dropSpaces · numSpaces |>.toString)
    |>.toList
    |> "\n".intercalate
where
  dropSpaces (line : Slice) (numSpaces : Nat) : Slice := Id.run do
    let mut line := line
    let mut numSpaces := numSpaces
    while numSpaces > 0 do
      if line.front != ' ' then
        break
      line := line.drop 1
      numSpaces := numSpaces - 1
    return line

namespace Lean

public structure Fmt.RawFormattedToken where
  formattedTrailingRange? : Option Syntax.Range

public structure Fmt.Context where
  env : Environment
  lineInfos : Array SyntaxLineInfo

public structure Fmt.State where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  tags : Std.HashMap Syntax.Range (Array TagId)
  rawFormattedTokens : Std.HashMap Syntax.Range RawFormattedToken

public structure Fmt.TaggedDoc where
  doc : Fmt.Doc

public abbrev FmtM α := ReaderT Fmt.Context (ExceptT Fmt.Error (StateT Fmt.State Id)) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

public def FmtM.run
    (env : Environment)
    (lineInfos : Array Fmt.SyntaxLineInfo)
    (act : FmtM α) :
    Except Fmt.Error (α × Std.HashMap Syntax.Range (Array Fmt.TagId) × Std.HashMap Syntax.Range Fmt.RawFormattedToken) := do
  let (v?, s) := ReaderT.run act { env, lineInfos }
    |>.run {
      shareCommonState := default
      freshTagId := Nat.zero
      tags := ∅
      rawFormattedTokens := ∅
    }
  return (← v?, s.tags, s.rawFormattedTokens)

instance : MonadShareCommon FmtM where
  withShareCommon v _ := modifyGet fun s =>
    let (v, shareCommonState) := s.shareCommonState.shareCommon v
    (v, { s with shareCommonState })

namespace Fmt

public def getLineInfo! (pos : String.Pos.Raw) : FmtM SyntaxLineInfo := do
  let ctx ← read
  let (_, lineInfo) := ctx.lineInfos.binSearchRightmost pos (·.startPos) (· < ·) |>.get!
  assert! lineInfo.startPos <= pos && pos < lineInfo.endPos
  return lineInfo

public def throwPartialFormatter : FmtM α :=
  throw <| .partialFormatter .anonymous

public def untagged (doc : Fmt.Doc) : TaggedDoc :=
  ⟨doc⟩

public def tagged (doc : Fmt.Doc) (ref : Syntax) : FmtM TaggedDoc := do
  let some range := ref.getRange?
    | return ⟨doc⟩
  let currentTagId : Nat := (← get).freshTagId
  modify fun s =>
    { s with
      freshTagId := currentTagId + 1
      tags := s.tags.alter range fun
        | none => some #[currentTagId]
        | some tags => some <| tags.push currentTagId
    }
  return ⟨.tagged currentTagId doc⟩

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
public def joinUsing (sep : TaggedDoc) (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .joinUsing sep.doc <| ds.map (·.doc)

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

def fmtRaw (stx : Syntax) : FmtM Doc := do
  let some pos := stx.getPos?
    | throw <| .malformedInputSyntax stx none "syntax has no head position"
  let some tailPos := stx.getTailPos?
    | throw <| .malformedInputSyntax stx none "syntax has no tail position"
  let firstRawLineIndentation := (← getLineInfo! pos).indentation
  let rawStx ← go firstRawLineIndentation tailPos stx
  return .nested rawStx
where
  go (firstRawLineIndentation : Nat) (lastTokenTailPos : String.Pos.Raw) (stx : Syntax) : FmtM Doc := do
    match stx with
    | .missing =>
      return .failure
    | .atom info val =>
      let some trailing := info.getTrailing?
        | addRawFormattedToken stx none
          return .text val
      let (trailing, formattedTrailingRange) := fmtTrailing firstRawLineIndentation lastTokenTailPos trailing
      addRawFormattedToken stx formattedTrailingRange
      return .text val ++ trailing
    | .ident info rawVal _ _ =>
      let some trailing := info.getTrailing?
        | addRawFormattedToken stx none
          return .text rawVal.toString
      let (trailing, formattedTrailingRange) := fmtTrailing firstRawLineIndentation lastTokenTailPos trailing
      addRawFormattedToken stx formattedTrailingRange
      return .text rawVal.toString ++ trailing
    | .node _ _ args =>
      let docs ← args.mapM (go firstRawLineIndentation lastTokenTailPos ·)
      return .join docs
  fmtTrailing
      (firstRawLineIndentation : Nat)
      (lastTokenTailPos : String.Pos.Raw)
      (trailing : Substring.Raw) :
      Doc × Syntax.Range := Id.run do
    let lines := trailing.splitOn "\n" |>.toArray
    let mut newLines := #[lines[0]!.toString]
    let mut formattedRange := ⟨trailing.startPos, trailing.stopPos⟩
    let isFinalTrailing := trailing.startPos >= lastTokenTailPos
    if isFinalTrailing then
      formattedRange := ⟨lines[0]!.startPos, lines[0]!.stopPos⟩
    else
      newLines := newLines ++ lines[1...*].toArray.map (·.toString.deindent (firstRawLineIndentation + 2))
    let formatted := newLines.map (Doc.text ·)
    return (Doc.joinUsing .hardNl formatted, formattedRange)
  addRawFormattedToken (stx : Syntax) (formattedTrailingRange? : Option Syntax.Range) : FmtM Unit := do
    let some range := stx.getInfo?.get!.getRange?
      | throw <| .malformedInputSyntax stx none "token has no range"
    modify fun s => { s with
      rawFormattedTokens := s.rawFormattedTokens.insert range { formattedTrailingRange? }
    }

/-
aaa (b +
  2)

aaa (
  b +
    2)

aaa + b / 2
aaa +
  b / 2

  aaa + b
    / 2

  aaa +
    b
      / 2
-/

public def fmt : Fmt := fun stx =>
  match stx with
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
      | let doc ← fmtRaw stx
        return ← tagged doc stx
    let r ← f stx
    try
      let r ← r.tag stx
      withShareCommon r
    catch e =>
      if let .partialFormatter errorKind _ := e then
        if errorKind == .anonymous then
          throw <| .partialFormatter kind
      throw e

def filterRawFormattedComments
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (rawFormattedTokens : Std.HashMap Syntax.Range RawFormattedToken) :
    Std.HashMap Syntax.Range (Array Comment) :=
  let comments := comments.map fun _ cs =>
    cs.filter fun c => Id.run do
      let some rawFormattedToken := rawFormattedTokens.get? c.originalTokenRange
        | return true
      let some formattedTrailingRange := rawFormattedToken.formattedTrailingRange?
        | return true
      dbg_trace c.content
      dbg_trace repr formattedTrailingRange
      dbg_trace repr c.originalTrailingRange
      return ! formattedTrailingRange.includes c.originalTrailingRange
  comments.filter fun _ cs => ! cs.isEmpty

/--
Associates all syntax ranges that have been tagged by `Fmt.fmt` with the portions of the rendered
string that a specific tagged sub-document has been rendered to.
Tagged syntax ranges that do not appear in the rendered string at all are removed.
-/
def connectTags
    {rendering : String.Slice}
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId))
    (tagsToRendered : Std.HashMap TagId (Std.HashSet rendering.Subslice)) :
    Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice) :=
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
  syntaxToTags.filterMap fun _ tags => do
    let mut ranges := {}
    for tag in tags do
      if let some rendered := tagsToRendered.get? tag then
        ranges := ranges.insertMany rendered
    guard <| ! ranges.isEmpty
    return ranges

public def main (env : Environment) (stx : Syntax) : Except Error String := do
  let lineInfos := collectSyntaxLineInfos stx
  let comments ← collectComments stx
  let (taggedDoc, syntaxToTags, rawFormattedTokens) ← FmtM.run env lineInfos <| fmt stx
  let comments := filterRawFormattedComments comments rawFormattedTokens
  let doc := taggedDoc.doc
  let some output := format? doc 100
    | throw <| .formattingFailure stx doc
  let tagsToRendered := output.tags
  let syntaxToRendered := connectTags syntaxToTags tagsToRendered
  let rendering := insertComments 100 output.rendering syntaxToRendered comments
  return rendering
