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
import Lean.Data.Fmt.Module
import Lean.Data.Fmt.Util
import Init.Data.Array.MinMax
import Init.Data.Range.Polymorphic.Iterators

partial def Lean.Syntax.getTailToken? (stx : Syntax) : Option Syntax :=
  match stx with
  | .missing => none
  | .atom ..
  | .ident .. => some stx
  | .node _ _ args => args.findSomeRev? getTailToken?

partial def Lean.Syntax.getHeadToken? (stx : Syntax) : Option Syntax :=
  match stx with
  | .missing => none
  | .atom ..
  | .ident .. => some stx
  | .node _ _ args => args.findSome? getHeadToken?

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

public structure Fmt.FormattedWhitespace where
  formattedLeadingRanges : Array Syntax.Range
  formattedTrailingRanges : Array Syntax.Range
  deriving Repr

def Fmt.FormattedWhitespace.merge (t1 t2 : Fmt.FormattedWhitespace) : Fmt.FormattedWhitespace where
  formattedLeadingRanges := t1.formattedLeadingRanges ++ t2.formattedLeadingRanges
  formattedTrailingRanges := t1.formattedTrailingRanges ++ t2.formattedTrailingRanges

public structure Fmt.Context where
  env : Environment
  opts : Options
  lineInfos : Array SyntaxLineInfo

public structure Fmt.State where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  tags : Std.HashMap Syntax.Range (Array TagId)
  formattedWhitespace : Std.HashMap Syntax.Range FormattedWhitespace
  rawFormattedKinds : Std.HashMap Syntax.Range SyntaxNodeKind

public structure Fmt.TaggedDoc where
  doc : Fmt.Doc
  deriving Inhabited

public abbrev FmtM α := ReaderT Fmt.Context (ExceptT Fmt.Error (StateT Fmt.State Id)) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

public def FmtM.run
    (env : Environment)
    (opts : Options)
    (lineInfos : Array Fmt.SyntaxLineInfo)
    (act : FmtM α) :
    Except Fmt.Error (α × Std.HashMap Syntax.Range (Array Fmt.TagId) × Std.HashMap Syntax.Range Fmt.FormattedWhitespace × Std.HashMap Syntax.Range SyntaxNodeKind) := do
  let (v?, s) := ReaderT.run act { env, opts, lineInfos }
    |>.run {
      shareCommonState := default
      freshTagId := Nat.zero
      tags := ∅
      formattedWhitespace := ∅
      rawFormattedKinds := ∅
    }
  return (← v?, s.tags, s.formattedWhitespace, s.rawFormattedKinds)

instance : MonadShareCommon FmtM where
  withShareCommon v _ := modifyGet fun s =>
    let (v, shareCommonState) := s.shareCommonState.shareCommon v
    (v, { s with shareCommonState })

namespace Fmt

public def getStxArg! (stx : Syntax) (i : Nat) : FmtM Syntax := do
  let arg := stx.getArg i
  if arg.isMissing then
    throw <| .partialFormatter
  return arg

public def getLineInfo! (pos : String.Pos.Raw) : FmtM SyntaxLineInfo := do
  let ctx ← read
  let (_, lineInfo) := ctx.lineInfos.binSearchRightmost pos (·.startPos) (· < ·) |>.get!
  assert! lineInfo.startPos <= pos && pos <= lineInfo.endPos
  return lineInfo

public def getLineInfos (pos tailPos : String.Pos.Raw) : FmtM (Array SyntaxLineInfo) := do
  let ctx ← read
  let (startIdx, _) := ctx.lineInfos.binSearchRightmost pos (·.startPos) (· < ·) |>.get!
  let (endIdx, _) := ctx.lineInfos.binSearchRightmost tailPos (·.startPos) (· < ·) |>.get!
  let lineInfos := ctx.lineInfos[startIdx...=endIdx].toArray
  assert! ! lineInfos.isEmpty
  return lineInfos

public def getNextLineInfo? (pos : String.Pos.Raw) : FmtM (Option SyntaxLineInfo) := do
  let ctx ← read
  let (i, _) := ctx.lineInfos.binSearchRightmost pos (·.startPos) (· < ·) |>.get!
  return ctx.lineInfos[i + 1]?

def getFormattedWhitespace? (tk : Syntax) : FmtM (Option FormattedWhitespace) := do
  let some range := tk.getInfo?.get!.getRange?
    | throw <| .malformedInputSyntax tk none "token has no range"
  return (← get).formattedWhitespace.get? range

def isWhitespaceFormatted (tk : Syntax) (whitespaceRange : Syntax.Range) : FmtM Bool := do
  let some ws ← getFormattedWhitespace? tk
    | return false
  return ws.formattedLeadingRanges.any (·.includes whitespaceRange)
    || ws.formattedTrailingRanges.any (·.includes whitespaceRange)

def addFormattedWhitespace
    (tk : Syntax)
    (formattedLeadingRanges : Array Syntax.Range)
    (formattedTrailingRanges : Array Syntax.Range) :
    FmtM Unit := do
  let some range := tk.getInfo?.get!.getRange?
    | throw <| .malformedInputSyntax tk none "token has no range"
  let newTk := {
    formattedLeadingRanges
    formattedTrailingRanges
  }
  modify fun s => { s with
    formattedWhitespace := s.formattedWhitespace.alter range fun
      | none => some newTk
      | some tk => some <| tk.merge newTk
  }

public def fmtWhitespace
    (stx : Syntax)
    (fmtLeading : Syntax → Substring.Raw → FmtM (Array (α × Option Syntax.Range)))
    (fmtTrailing : Syntax → Substring.Raw → FmtM (Array (β × Option Syntax.Range))) :
    FmtM (Array α × Array β) := do
  let leadingFmt ← (do
    let some leadingTk := stx.getHeadToken?
      | pure #[]
    let some leading := leadingTk.getLeading?
      | pure #[]
    let leadingResult ← fmtLeading leadingTk leading
    let leadingResult ← leadingResult.filterM fun (_, formattedLeading?) => do
      let some formattedLeading := formattedLeading?
        | return true
      return ! (← isWhitespaceFormatted leadingTk formattedLeading)
    let leadingFmt := leadingResult.map (·.1)
    let formattedLeading := leadingResult.filterMap (·.2)
    addFormattedWhitespace leadingTk formattedLeading #[]
    pure leadingFmt)
  let trailingFmt ← (do
    let some trailingTk := stx.getTailToken?
      | pure #[]
    let some trailing := trailingTk.getTrailing?
      | pure #[]
    let trailingResult ← fmtTrailing trailingTk trailing
    let trailingResult ← trailingResult.filterM fun (_, formattedTrailing?) => do
      let some formattedTrailing := formattedTrailing?
        | return true
      return ! (← isWhitespaceFormatted trailingTk formattedTrailing)
    let trailingFmt := trailingResult.map (·.1)
    let formattedTrailing := trailingResult.filterMap (·.2)
    addFormattedWhitespace trailingTk #[] formattedTrailing
    pure trailingFmt)
  return (leadingFmt, trailingFmt)

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
public def empty : TaggedDoc :=
  untagged .empty
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
public def unindented (unindentToLineIndentation : Bool) (d : TaggedDoc) : TaggedDoc :=
  untagged <| .unindented unindentToLineIndentation d.doc
public def either (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .either a.doc b.doc
public def oneOf (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .oneOf <| ds.map (·.doc)
public def append (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .append a.doc b.doc
public def join (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .join <| ds.map (·.doc)
public def joinUsing (sep : TaggedDoc) (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .joinUsing sep.doc <| ds.map (·.doc)
public def fillUsing (sep : TaggedDoc) (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .fillUsing sep.doc <| ds.map (·.doc)
public def fillUsingSpace (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .fillUsingSpace <| ds.map (·.doc)

public instance : Append TaggedDoc where
  append := append

public structure Sep where
  s : TaggedDoc
  wrap : TaggedDoc → TaggedDoc := id

public instance : Coe TaggedDoc Sep where
  coe s := { s }

public structure Component where
  sepBefore? : Option Sep := none
  doc? : Option TaggedDoc
  sepAfter? : Option Sep := none

public instance : Coe (Option TaggedDoc) Component where
  coe doc? := { doc? }

public def Component.withSepBefore (doc? : Option TaggedDoc) (sepBefore : Sep) : Component where
  sepBefore? := some sepBefore
  doc?

public def Component.withSepAfter (doc? : Option TaggedDoc) (sepAfter : Sep) : Component where
  doc?
  sepAfter? := some sepAfter

public def combine (cs : Array Component) : TaggedDoc := Id.run do
  let mut entries : Array (Option Sep × TaggedDoc × Option Sep) :=
    cs.filterMap fun c => do
      let d ← c.doc?
      guard <| ! d.doc.isAlwaysEmpty
      return (c.sepBefore?, d, c.sepAfter?)
  if entries.isEmpty then
    return empty
  if let #[(_, doc, _)] := entries then
    return doc
  entries := entries.modify 0 fun (_, doc, sepAfter?) => (none, doc, sepAfter?)
  entries := entries.modify (entries.size - 1) fun (sepBefore?, doc, _) => (sepBefore?, doc, none)
  for i in (0...entries.size-1) do
    let (_, _, some _currSepAfter) := entries[i]!
      | continue
    let (some _nextSepBefore, _, _) := entries[i + 1]!
      | continue
    entries := entries.modify i fun (currSepBefore?, currDoc, _) => (currSepBefore?, currDoc, none)
  let mut combined := empty
  for (sepBefore?, doc, sepAfter?) in entries.reverse do
    if let some sepAfter := sepAfter? then
      combined := sepAfter.s ++ combined
      combined := sepAfter.wrap combined
    combined := doc ++ combined
    if let some sepBefore := sepBefore? then
      combined := sepBefore.s ++ combined
      combined := sepBefore.wrap combined
  return combined

public unsafe builtin_initialize fmtAttribute : KeyedDeclsAttribute Fmt ←
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
      if ! (builtin && (env.find? id).isSome || Parser.isValidSyntaxNodeKind env id || id == moduleKind || id == cmdsKind || id == headerKind) then
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
  deriving BEq

def InfixOperatorAssociativity.ofKind? (env : Environment) (opts : Options)
    (kind : SyntaxNodeKind) : Option InfixOperationAssociativity := do
  let info ← env.find? kind
  guard <| info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr
  let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
  let ParserDescr.trailingNode _ prec lhsPrec
      (ParserDescr.binary `andthen (ParserDescr.symbol _)
      (ParserDescr.cat `term rhsPrec)) := descr
    | none
  let isInfixl := prec == lhsPrec && lhsPrec + 1 == rhsPrec
  if isInfixl then
    return .left
  let isInfixr := prec == rhsPrec && lhsPrec == rhsPrec + 1
  if isInfixr then
    return .right
  let isInfix := prec + 1 == lhsPrec && lhsPrec == rhsPrec
  if isInfix then
    return .middle
  none

inductive InfixOperatorChainLink where
  | operand (stx : Syntax)
  | operator (stx : Syntax)

variable (env : Environment) (opts : Options) (chainAssoc : InfixOperationAssociativity) in
partial def infixOperatorChain (stx : Syntax) : Array InfixOperatorChainLink := Id.run do
  if stx.getNumArgs != 3 then
    return #[.operand stx]
  let left := stx[0]
  let op := stx[1]
  let right := stx[2]
  if ! op.isAtom then
    return #[.operand stx]
  let some stxAssoc := InfixOperatorAssociativity.ofKind? env opts stx.getKind
    | return #[.operand stx]
  if stxAssoc != chainAssoc then
    return #[.operand stx]
  let leftChain :=
    if chainAssoc matches .left then
      infixOperatorChain left
    else
      #[.operand left]
  let rightChain :=
    if chainAssoc matches .right then
      infixOperatorChain right
    else
      #[.operand right]
  return leftChain ++ #[.operator op] ++ rightChain

structure fmtRaw.Context where
  rawIndentation : Nat
  firstTokenPos : String.Pos.Raw
  lastTokenTailPos : String.Pos.Raw

mutual

partial def fmtChoiceNode : Fmt := fun stx => do
  if stx.getNumArgs == 0 then
    return ← text "" stx
  fmt stx[0]

partial def fmtInfixOperator (env : Environment) (opts : Options) (assoc : InfixOperationAssociativity) : Fmt := fun stx => do
  let chain := infixOperatorChain env opts assoc stx
  let chain ← chain.mapM fun
    | .operator stx => do
      return Fmt.nl ++ (← Fmt.fmt stx) ++ Fmt.space
    | .operand stx => do
      let operand ← Fmt.fmt stx
      return Fmt.nested operand
    let doc := Fmt.nested <| Fmt.join chain
    return Fmt.maybeFlattened doc

public partial def getFormatterForKind? (env : Environment) (opts : Options) (kind : SyntaxNodeKind) : Option Fmt := do
  if kind == choiceKind then
    return fmtChoiceNode
  match fmtAttribute.getValues env kind |>.head? with
  | none =>
    let assoc ← InfixOperatorAssociativity.ofKind? env opts kind
    return fmtInfixOperator env opts assoc
  | some fmt =>
    return fmt

public partial def fmtRaw : Fmt := fun stx => do
  let some pos := stx.getPos?
    | return ← text "" stx
  let some tailPos := stx.getTailPos?
    | return ← text "" stx
  modify fun s => { s with
    rawFormattedKinds := s.rawFormattedKinds.insert ⟨pos, tailPos⟩ stx.getKind
  }
  let lineInfos ← getLineInfos pos tailPos
  let rawIndentation := lineInfos.map (·.indentation) |>.min?.get!
  let mut rawDoc ← go stx |>.run {
    rawIndentation
    firstTokenPos := pos
    lastTokenTailPos := tailPos
  }
  -- The use of `unindented (unindentToLineIndentation := true)`
  -- ensures that regardless of where `rawDoc` is placed by the auto-formatter,
  -- the indentation of each line of `rawDoc` *relative* to its least indented line
  -- remains the same in the output.
  -- This is crucial for ensuring that raw formatting is idempotent, since a second
  -- formatting call will again determine the indentation relative to its least
  -- indented line.
  -- Without this primitive, outer `nested` nodes can change the relative indentation
  -- of the raw formatted syntax.
  rawDoc := unindented (unindentToLineIndentation := true) rawDoc
  rawDoc.tag stx
where
  go (stx : Syntax) : ReaderT fmtRaw.Context FmtM TaggedDoc := do
    match stx with
    | .missing =>
      return failure
    | .atom _ val =>
      fmtToken stx val
    | .ident _ rawVal _ _ =>
      fmtToken stx rawVal.toString
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      let docs ← args.mapM go
        return join docs
  fmtToken (stx : Syntax) (token : String) :
      ReaderT fmtRaw.Context FmtM TaggedDoc := do
    let ctx ← read
    let (leadingDocs, trailingDocs) ← fmtWhitespace stx (fmtLeading ctx) (fmtTrailing ctx)
    let valDocs := token.split "\n" |>.map (.text ·.toString) |>.toArray
    let valDoc := .joinUsing .hardNl valDocs
    let mut doc ← tagged valDoc stx
    if let #[leadingDoc] := leadingDocs then
      doc := leadingDoc ++ doc
    if let #[trailingDoc] := trailingDocs then
      doc := doc ++ trailingDoc
    return doc
  fmtTrailing
      (ctx : fmtRaw.Context)
      (_trailingTk : Syntax)
      (trailing : Substring.Raw) :
      FmtM (Array (TaggedDoc × Option Syntax.Range)) := do
    let isFinalTrailing := trailing.startPos >= ctx.lastTokenTailPos
    if isFinalTrailing then
      return #[]
    let lines := trailing.splitOn "\n" |>.toArray
    let removedIndentation := ctx.rawIndentation
    let newLines := #[lines[0]!.toString]
      ++ lines[1...*].toArray.map (·.toString.deindent removedIndentation)
    let formatted := newLines.map (Doc.text ·)
    return #[(untagged <| Doc.joinUsing .hardNl formatted, some <| .ofSubstring trailing)]
  fmtLeading
      (ctx : fmtRaw.Context)
      (_leadingTk : Syntax)
      (leading : Substring.Raw) :
      FmtM (Array (TaggedDoc × Option Syntax.Range)) := do
    let isInitialLeading := leading.stopPos <= ctx.firstTokenPos
    if isInitialLeading then
      return #[]
    let lines := leading.splitOn "\n" |>.toArray
    let removedIndentation := ctx.rawIndentation
    let newLines := lines.map (·.toString.deindent removedIndentation)
    let formatted := newLines.map (Doc.text ·)
    return #[(untagged <| Doc.joinUsing .hardNl formatted, some <| .ofSubstring leading)]

public partial def fmtWith (f : Fmt) : Fmt := fun stx => do
  try
    let r ← f stx
    let r ← r.tag stx
    withShareCommon r
  catch e =>
    if let .partialFormatter _ := e then
      let r ← fmtRaw stx
      return r
    throw e

public partial def fmt : Fmt := fun stx =>
  match stx with
  | .missing =>
    pure <| failure
  | .atom _ val =>
    let valDocs := val.split "\n" |>.map (Doc.text ·.toString) |>.toArray
    let valDoc := .joinUsing .hardNl valDocs
    tagged valDoc stx
  | .ident _ rawVal _ _ =>
    let valDocs := rawVal.toString.split "\n" |>.map (Doc.text ·.toString) |>.toArray
    let valDoc := .joinUsing .hardNl valDocs
    tagged valDoc stx
  | .node .. => do
    let ctx ← read
    let kind := stx.getKind
    let some f := getFormatterForKind? ctx.env ctx.opts kind
      | let doc ← fmtRaw stx
        return doc
    fmtWith f stx

end

public def fmt? (stx? : Option Syntax) : FmtM (Option Fmt.TaggedDoc) :=
  stx?.mapM fmt

public def fmtWith? (f : Fmt) (stx? : Option Syntax) : FmtM (Option Fmt.TaggedDoc) :=
  stx?.mapM (fmtWith f)

public def fmtArray {ks : SyntaxNodeKinds}
    (array : TSyntaxArray ks) :
    FmtM (Array TaggedDoc) :=
  array.mapM fmt

public def fmtArrayWith {ks : SyntaxNodeKinds}
    (f : Fmt) (array : TSyntaxArray ks) :
    FmtM (Array TaggedDoc) :=
  array.mapM (fmtWith f)

public inductive SepArrayFormat
  | joinUsingSep (afterElem? afterSep? : Option TaggedDoc)
  | joinUsingNl (allowFlattening : Bool) (afterElem? : Option TaggedDoc := none)
  | fillUsingSep (afterElem? afterSep? : Option TaggedDoc)

public def fmtSepArrayDocs
    (sepArrayDocs : Array TaggedDoc)
    (format : SepArrayFormat)
    : TaggedDoc :=
  match format with
  | .joinUsingSep afterElem? afterSep? =>
    joinUsingSep afterElem? afterSep?
  | .joinUsingNl allowFlattening afterElem? =>
    let joinedUsingNl := joinUsingNl afterElem?
    if allowFlattening then
      oneOf #[
        flattened <| joinUsingSep afterElem? (afterSep? := space),
        joinedUsingNl
      ]
    else
      joinedUsingNl
  | .fillUsingSep afterElem? afterSep? =>
    fillUsingSep afterElem? afterSep?

where

  joinUsingSep (afterElem? afterSep? : Option TaggedDoc) : TaggedDoc :=
    let docs := sepArrayDocs.mapIdx fun i doc => Id.run do
      if i == sepArrayDocs.size - 1 then
        return doc
      let isElem := i % 2 == 0
      let afterDoc? :=
        if isElem then
          afterElem?
        else
          afterSep?
      let some afterDoc := afterDoc?
        | return doc
      return doc ++ afterDoc
    join docs

  joinUsingNl (afterElem? : Option TaggedDoc) : TaggedDoc := Id.run do
    let mut (elems, _) := split
    if let some afterElem := afterElem? then
      elems := elems.mapIdx fun i elem =>
        if i == elems.size - 1 then
          elem
        else
          elem ++ afterElem
    return joinUsing hardNl elems

  fillUsingSep (afterElem? afterSep? : Option TaggedDoc) : TaggedDoc := Id.run do
    let afterElem := afterElem?.getD empty
    let afterSep := afterSep?.getD empty
    let (elems, seps) := split
    if elems.size == 0 then
      return empty
    let hd := elems[0]!
    if elems.size == 1 then
      return hd
    let mut lastFlattened : TaggedDoc := flattened hd
    let mut lastNotFlattened : TaggedDoc := hd
    for elem in elems[1...*], sep in seps do
      let lastMaybeFlattened := oneOf #[lastFlattened, lastNotFlattened]
      lastFlattened := oneOf #[
        join #[lastFlattened, afterElem, sep, afterSep, flattened elem],
        join #[lastMaybeFlattened, afterElem, sep, afterSep, hardNl, flattened elem]
      ]
      lastNotFlattened := join #[lastMaybeFlattened, afterElem, sep, afterSep, hardNl, elem]
    return oneOf #[lastFlattened, lastNotFlattened]

  split : Array TaggedDoc × Array TaggedDoc := Id.run do
    let mut elems := #[]
    let mut seps := #[]
    for h:i in (0...sepArrayDocs.size) do
      let doc := sepArrayDocs[i]
      if i % 2 == 0 then
        elems := elems.push doc
      else
        seps := seps.push doc
    return (elems, seps)

public def fmtSepArray
    {sep : String}
    (sepArray : Syntax.SepArray sep) (format : SepArrayFormat) :
    FmtM TaggedDoc := do
  let elemsAndSeps ← sepArray.elemsAndSeps.mapM fmt
  return fmtSepArrayDocs elemsAndSeps format

public def fmtTSepArray
    {ks : SyntaxNodeKinds} {sep : String}
    (sepArray : Syntax.TSepArray ks sep) (format : SepArrayFormat) :
    FmtM TaggedDoc := do
  let elemsAndSeps ← sepArray.elemsAndSeps.mapM fmt
  return fmtSepArrayDocs elemsAndSeps format
