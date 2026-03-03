/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.KeyedDeclsAttribute
public import Lean.Util.ShareCommon
public import Lean.Data.Fmt.LineInfo
import Lean.Parser.Extension
import Lean.ExtraModUses
import Lean.Elab.InfoTree.Main
import Lean.Data.Fmt.RangeTree

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
  opts : Options
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
    (opts : Options)
    (lineInfos : Array Fmt.SyntaxLineInfo)
    (act : FmtM α) :
    Except Fmt.Error (α × Std.HashMap Syntax.Range (Array Fmt.TagId) × Std.HashMap Syntax.Range Fmt.RawFormattedToken) := do
  let (v?, s) := ReaderT.run act { env, opts, lineInfos }
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
  assert! lineInfo.startPos <= pos && pos <= lineInfo.endPos
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

public inductive InfixOperationAssociativity where
  | left
  | right
  | middle

inductive InfixOperatorChainLink where
  | operand (stx : Syntax)
  | operator (stx : Syntax)

variable (assoc : InfixOperationAssociativity) in
partial def infixOperatorChain (stx : Syntax) : Array InfixOperatorChainLink := Id.run do
  if stx.getNumArgs != 3 then
    return #[.operand stx]
  let left := stx[0]
  let op := stx[1]
  let right := stx[2]
  if ! op.isAtom then
    return #[.operand stx]
  let leftChain :=
    if assoc matches .left then
      infixOperatorChain left
    else
      #[.operand left]
  let rightChain :=
    if assoc matches .right then
      infixOperatorChain right
    else
      #[.operand right]
  return leftChain ++ #[.operator op] ++ rightChain

mutual

partial def fmtInfixOperator (assoc : InfixOperationAssociativity) : Fmt := fun stx => do
  let chain := infixOperatorChain assoc stx
    let chain ← chain.mapM fun
      | .operator stx => do
        return Fmt.nl ++ (← Fmt.fmt stx) ++ Fmt.space
      | .operand stx => do
        let operand ← Fmt.fmt stx
        return Fmt.nested operand
    let doc := Fmt.nested <| Fmt.join chain
    return Fmt.maybeFlattened doc

partial def interpretParserDescr? (descr : ParserDescr) : Option Fmt := do
  let ParserDescr.trailingNode _ prec lhsPrec
      (ParserDescr.binary `andthen (ParserDescr.symbol _)
      (ParserDescr.cat `term rhsPrec)) := descr
    | none
  let isInfixl := prec == lhsPrec && lhsPrec + 1 == rhsPrec
  let isInfixr := prec == rhsPrec && lhsPrec == rhsPrec + 1
  let isInfix := prec + 1 == lhsPrec && lhsPrec == rhsPrec
  if isInfixl then
    return fmtInfixOperator .left
  else if isInfixr then
    return fmtInfixOperator .right
  else if isInfix then
    return fmtInfixOperator .middle
  else
    none

partial def getFormatterForKind? (env : Environment) (opts : Options) (kind : SyntaxNodeKind) : Option Fmt := do
  match fmtAttribute.getValues env kind |>.head? with
  | none =>
    let info ← env.find? kind
    guard <| info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr
    let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
    interpretParserDescr? descr
  | some fmt =>
    return fmt

partial def fmtRaw : Fmt := fun stx => do
  let some pos := stx.getPos?
    | throw <| .malformedInputSyntax stx none "syntax has no head position"
  let some tailPos := stx.getTailPos?
    | throw <| .malformedInputSyntax stx none "syntax has no tail position"
  let firstRawLineIndentation := (← getLineInfo! pos).indentation
  let rawDoc ← go firstRawLineIndentation tailPos stx
  nested rawDoc |>.tag stx
where
  go (firstRawLineIndentation : Nat) (lastTokenTailPos : String.Pos.Raw) : Fmt := fun stx => do
    match stx with
    | .missing =>
      return failure
    | .atom info val =>
      let some trailing := info.getTrailing?
        | addRawFormattedToken stx none
          return untagged <| .text val
      let (trailing, formattedTrailingRange) := fmtTrailing firstRawLineIndentation lastTokenTailPos trailing
      addRawFormattedToken stx formattedTrailingRange
      return untagged <| .text val ++ trailing
    | .ident info rawVal _ _ =>
      let some trailing := info.getTrailing?
        | addRawFormattedToken stx none
          return untagged <| .text rawVal.toString
      let (trailing, formattedTrailingRange) := fmtTrailing firstRawLineIndentation lastTokenTailPos trailing
      addRawFormattedToken stx formattedTrailingRange
      return untagged <| .text rawVal.toString ++ trailing
    | .node _ kind args =>
      if getFormatterForKind? (← read).env (← read).opts kind |>.isSome then
        let doc ← fmt stx
        return doc
      let docs ← args.mapM (go firstRawLineIndentation lastTokenTailPos ·)
      return join docs
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
      if lines.size > 0 then
        -- Include newline in range
        formattedRange := ⟨lines[0]!.startPos, lines[0]!.stopPos.increaseBy 1⟩
      else
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

public partial def fmt : Fmt := fun stx =>
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
    let some f := getFormatterForKind? ctx.env ctx.opts kind
      | let doc ← fmtRaw stx
        return doc
    let r ← f stx
    try
      let r ← r.tag stx
      withShareCommon r
    catch e =>
      if let .partialFormatter errorKind _ := e then
        if errorKind == .anonymous then
          throw <| .partialFormatter kind
      throw e

end
