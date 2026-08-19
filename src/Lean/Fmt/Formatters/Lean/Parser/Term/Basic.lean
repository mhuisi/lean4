/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Term.Basic
import Init.Data
import Lean.Fmt.Util.Basic

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Term.hole]
public def fmtHole : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.syntheticHole]
public def fmtSyntheticHole : Fmt := fun
  | `(Parser.Term.syntheticHole| ?%$questionTk $id:ident) => do
    let questionTk ← fmt questionTk
    let id ← fmt id
    return Layouts.atomic #[questionTk, id]
  | `(Parser.Term.syntheticHole| ?%$questionTk _%$holeTk) => do
    let questionTk ← fmt questionTk
    let holeTk ← fmt holeTk
    return Layouts.atomic #[questionTk, holeTk]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.omission]
public def fmtOmission : Fmt := fmtAtomic

meta def explicitBinderF := Parser.Term.explicitBinder
meta def implicitBinderF := Parser.Term.implicitBinder
meta def strictImplicitBinderF := Parser.Term.strictImplicitBinder

public abbrev binderKinds : List Name := [
  `ident,
  ``Parser.Term.hole,
  ``Parser.Term.bracketedBinder
]

private inductive BinderKind where
  | explicit
  | implicit
  | instance
deriving BEq, Inhabited

private def BinderKind.classify (binder : TSyntax binderKinds) : BinderKind :=
  match binder.raw.getKind with
  | ``Parser.Term.strictImplicitBinder
  | ``Parser.Term.implicitBinder => .implicit
  | ``Parser.Term.instBinder => .instance
  | _ => .explicit

private structure BinderWithDependents where
  binder : TSyntax binderKinds
  dependents : Std.HashSet Nat
deriving BEq, Inhabited

/--
Splits `binder` into the variables bound by it and the syntax in which variables bound by
preceding binders may be referenced.
-/
private def splitBinder (binder : TSyntax binderKinds) : Array Name × Array Syntax :=
  if binder.raw.isIdent then
    (#[binder.raw.getId], #[])
  else
    match binder.raw with
    | `(explicitBinderF| ($ids* $[: $type?:term]? $[$tacticOrDefault?]?)) =>
      (binderIdentNames ids, type?.toArray.map (·.raw) ++ tacticOrDefault?.toArray.map (·.raw))
    | `(implicitBinderF| {$ids* $[: $type?:term]?})
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
      (binderIdentNames ids, type?.toArray.map (·.raw))
    | `(Parser.Term.instBinder| [$[$id?:ident :]? $classType:term]) =>
      (id?.toArray.map (·.getId), #[classType.raw])
    | _ =>
      (#[], #[])
where
  binderIdentNames (ids : Array Syntax) : Array Name :=
    ids.filterMap fun id => if id.isIdent then some id.getId else none

/--
Checks whether `stx` contains an identifier that refers to one of `vars`.
Identifiers that merely have one of `vars` as a prefix are considered references as well so that
generalized field notation such as `xs.size` is accounted for.
-/
private partial def referencesVars (vars : Array Name) : Syntax → Bool
  | .ident _ _ id _ => vars.any (·.isPrefixOf id)
  | .node _ _ args  => args.any (referencesVars vars)
  | _               => false

/--
Pairs every binder in `binders` with the indices of the later binders that reference one of the
variables bound by it.
-/
private def computeBinderDependents
    (binders : TSyntaxArray binderKinds)
    : Array BinderWithDependents := Id.run do
  let splitBinders := binders.map splitBinder
  let mut result := Array.emptyWithCapacity binders.size
  for i in 0...binders.size do
    let (boundVars, _) := splitBinders[i]!
    let mut dependents := {}
    if ! boundVars.isEmpty then
      for j in (i + 1)...binders.size do
        let (_, body) := splitBinders[j]!
        if body.any (referencesVars boundVars) then
          dependents := dependents.insert j
    result := result.push ⟨binders[i]!, dependents⟩
  return result

private structure BinderGroupInProgress where
  binders : Array Syntax
  dependents : Std.HashSet Nat
  kind : BinderKind
deriving Inhabited, BEq

private def BinderGroupInProgress.init (b : BinderWithDependents) : BinderGroupInProgress := {
  binders := #[b.binder]
  dependents := b.dependents
  kind := .classify b.binder
}

mutual

public def fmtBinder
    (lbTks : Array Syntax)
    (lhses : Array Syntax)
    (subBinders : TSyntaxArray binderKinds)
    (typeAscriptionTk? : Option Syntax)
    (type? : Option (TSyntax `term))
    (tacticOrDefault? : Option (TSyntax [``Parser.Term.binderTactic, ``Parser.Term.binderDefault]))
    (rbTks : Array Syntax)
    (kind : Layouts.Types.SignatureKind := Layouts.Types.SignatureKind.local)
    : FmtM TaggedDoc := do
  let lbTks ← lbTks.mapM fmt
  let lhses ← lhses.mapM fmt
  let subBinderGroups ← fmtBinders subBinders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  let (colonEqTk?, default?) := Option.split <| ← tacticOrDefault?.mapM fun
    | `(Parser.Term.binderTactic| :=%$colonEqTk by%$byTk $tacticSeq) => do
      let colonEqTk ← fmt colonEqTk
      let byTk ← fmt byTk
      let tacticSeq ← fmt tacticSeq
      return (colonEqTk, Layouts.keywordPrefixedSeq byTk tacticSeq .sticky)
    | `(Parser.Term.binderDefault| :=%$colonEqTk $term) => do
      let colonEqTk ← fmt colonEqTk
      let term ← fmt term
      return (colonEqTk, term)
    | _ => throw .partialFormatter
  let colonEqTk? := colonEqTk?.getD empty
  let default? := default?.getD empty
  let rbTks ← rbTks.mapM fmt
  return Layouts.binder lbTks lhses subBinderGroups typeAscriptionTk? type? colonEqTk? default? rbTks kind

@[builtin_fmt Lean.Parser.Term.explicitBinder]
public def fmtExplicitBinder : Fmt := fun
  | `(explicitBinderF| (%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? $[$tacticOrDefault?]? )%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? tacticOrDefault? #[rbTk]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.implicitBinder]
public def fmtImplicitBinder : Fmt := fun
  | `(implicitBinderF| {%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.strictImplicitBinder]
public def fmtStrictImplicitBinder : Fmt := fun
  | `(strictImplicitBinderF| {%$lbTk1 {%$lbTk2 $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk1 }%$rbTk2) =>
    fmtBinder #[lbTk1, lbTk2] ids #[] typeAscriptionTk? type? none #[rbTk1, rbTk2] (kind := .global)
  | `(strictImplicitBinderF| {%$lbTk1 {%$lbTk2 $ids* $[:%$typeAscriptionTk? $type?:term]? ⦄%$rbTk) =>
    fmtBinder #[lbTk1, lbTk2] ids #[] typeAscriptionTk? type? none #[rbTk] (kind := .global)
  | `(strictImplicitBinderF| ⦃%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? }%$rbTk1 }%$rbTk2) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk1, rbTk2] (kind := .global)
  | `(strictImplicitBinderF| ⦃%$lbTk $ids* $[:%$typeAscriptionTk? $type?:term]? ⦄%$rbTk) =>
    fmtBinder #[lbTk] ids #[] typeAscriptionTk? type? none #[rbTk] (kind := .global)
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.instBinder]
public def fmtInstBinder : Fmt := fun
  | `(Parser.Term.instBinder| [%$lbTk $[$id?:ident :%$typeAscriptionTk?]? $classType:term ]%$rbTk) =>
    fmtBinder #[lbTk] id?.toArray #[] typeAscriptionTk? classType none #[rbTk]
  | _ =>
    throw .partialFormatter

public def groupBinders
    (binders : TSyntaxArray binderKinds)
    : BinderGroups := Id.run do
  if binders.isEmpty then
    return #[]
  let binders := computeBinderDependents binders
  let mut groups : BinderGroups := #[]
  let mut group : BinderGroupInProgress := .init binders[0]!
  for i in (1...binders.size) do
    let b := binders[i]!
    let kind : BinderKind := .classify b.binder
    match group.kind, kind with
    | .implicit, .implicit
    | .instance, .instance
    | .implicit, .instance =>
      group := extendGroup group b
    | .implicit, .explicit
    | .explicit, .instance
    | .explicit, .explicit =>
      if group.dependents.contains i then
        group := extendGroup group b
      else
        (groups, group) := finalizeGroup groups group b
    | .explicit, .implicit
    | .instance, .explicit
    | .instance, .implicit =>
      (groups, group) := finalizeGroup groups group b
  groups := groups.push group.binders
  return groups
where
  extendGroup (group : BinderGroupInProgress) (b : BinderWithDependents) : BinderGroupInProgress := {
    group with
    binders := group.binders.push b.binder
    dependents := group.dependents.union b.dependents
    kind := .classify b.binder
  }
  finalizeGroup (groups : BinderGroups) (group : BinderGroupInProgress) (b : BinderWithDependents)
      : BinderGroups × BinderGroupInProgress :=
    let groups := groups.push group.binders
    let group := .init b
    (groups, group)

public def fmtBinders
    (binders : TSyntaxArray binderKinds)
    : FmtM (Array (Array TaggedDoc)) := do
  let binderGroups := groupBinders binders
  let binderGroups ← binderGroups.mapM fun binderGroup => binderGroup.mapM fmt
  return binderGroups

end

public def fmtLocalSignature
    (lval : Syntax)
    (binders : TSyntaxArray binderKinds)
    (typeAscriptionTk? : Option Syntax)
    (type? : Option Syntax)
    : FmtM TaggedDoc := do
  let lval ← fmt lval
  let binders ← fmtBinders binders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.localSignature #[lval] binders typeAscriptionTk? type?

public def fmtGlobalSignature
    (lval : Syntax)
    (binders : TSyntaxArray binderKinds)
    (typeAscriptionTk? : Option Syntax)
    (type? : Option Syntax)
    : FmtM TaggedDoc := do
  let lval ← fmt lval
  let binders ← fmtBinders binders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.globalSignature #[lval] binders typeAscriptionTk? type?

@[builtin_fmt Lean.Parser.Term.structInstArrayRef]
public def fmtStructInstArrayRef : Fmt := fun
  | `(Parser.Term.structInstArrayRef| [%$lbTk $idx:term ]%$rbTk) => do
    let lbTk ← fmt lbTk
    let idx ← fmt idx
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk idx rbTk <| .sparse «break» (stickynessKind := .coequal)
  | _ => throw .partialFormatter

@[expose]
public def structInstLValKinds := [`ident, `fieldIdx, ``Parser.Term.structInstArrayRef]

public structure StructInstLValElem where
  dotTk? : Option Syntax
  elem : Syntax

public def splitStructInstLValIdent (id : TSyntax `ident) : Array StructInstLValElem := Id.run do
  -- The Lean parser parses LVals that consist purely of dots as identifiers, and the elaborator
  -- then splits these identifiers into fields.
  -- Since LVals can in principle become quite complex (e.g. with array references),
  -- we split these identifiers into their components so that we can still format them
  -- as separate components.
  -- In some cases, splitting an identifier into its components is not possible, e.g. when the
  -- identifier contains macro scopes, in which case we fall back to not attempting to split it.
  let some (comps, seps) := Syntax.identComponents? id
    | return #[⟨none, id⟩]
  let comps := comps.toArray
  let seps := seps.toArray
  -- comps.size - 1 = seps.size
  let mut r := #[⟨none, comps[0]!⟩]
  for i in (1...comps.size) do
    r := r.push ⟨seps[i - 1]!, comps[i]!⟩
  return r

public def splitStructInstLValRhs (rhs : Syntax) : FmtM (Array StructInstLValElem) := do
  rhs.getArgs.flatMapM fun rhsElem => do
    let kind := rhsElem.getKind
    if kind == groupKind then
      let dotTk ← getStxArg! rhsElem 0
      let elem ← getStxArg! rhsElem 1
      let elemKind := elem.getKind
      if elemKind == `ident then
        return splitStructInstLValIdent ⟨elem⟩ |>.modify 0 ({· with dotTk? := dotTk})
      else if elemKind == `fieldIdx then
        return #[⟨dotTk, elem⟩]
      else
        throw .partialFormatter
    else if kind == ``Parser.Term.structInstArrayRef then
      return #[⟨none, rhsElem⟩]
    else
      throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.structInstLVal]
public def fmtStructInstLVal : Fmt := fun stx => do
  let lhs ← getStxArg! stx 0
  if ! structInstLValKinds.contains lhs.getKind then
    throw .partialFormatter
  let lhs : TSyntax structInstLValKinds := ⟨lhs⟩
  let lhsElems : Array StructInstLValElem :=
    if let `($id:ident) := lhs then
      splitStructInstLValIdent id
    else
      #[⟨none, lhs⟩]
  let rhs ← getStxArg! stx 1
  let rhsElems ← splitStructInstLValRhs rhs
  let elems := lhsElems ++ rhsElems
  let elemComponents : Array TaggedDoc.Component ← elems.flatMapM fun e => do
    let dotTk? ← fmt? e.dotTk?
    let elem ← fmt e.elem
    return #[.withSepBefore dotTk? «break», elem]
  return nested <| maybeFlattened <| combine elemComponents

public def convertStructInstFieldBinders
    (binders : TSyntaxArray ``Parser.Term.structInstFieldBinder) :
    TSyntaxArray binderKinds :=
  binders.map fun
    | `(Parser.Term.structInstFieldBinder| $id:ident) => id
    | `(Parser.Term.structInstFieldBinder| $hole:hole) => hole
    | `(Parser.Term.structInstFieldBinder| $bracketedBinder:bracketedBinder) => bracketedBinder

public structure StructInstFieldDecl where
  format (signature : TaggedDoc) : TaggedDoc
deriving Inhabited, TypeName

public def mkStructInstFieldDecl (format : (signature : TaggedDoc) → TaggedDoc) : TaggedDoc :=
  failure.addMetaData (StructInstFieldDecl.mk format) fun v f => {
    v with
    format signature := propagateMetaData (v.format signature) f
  }

public def getStructInstFieldDecl? (doc : TaggedDoc) : Option StructInstFieldDecl :=
  doc.getMetaData? StructInstFieldDecl

@[builtin_fmt Lean.Parser.Term.structInstField]
public def fmtStructInstField : Fmt := fun
  | `(Parser.Term.structInstField|
      $lval:structInstLVal $[$binders?:structInstFieldBinder* $[:%$typeAscriptionTk? $type?:term]?
        $structInstFieldDecl?:structInstFieldDecl]?) => do
    let binders := convertStructInstFieldBinders <| binders?.getD #[]
    let typeAscriptionTk? := typeAscriptionTk?.join
    let type? := type?.join
    let signature ← fmtLocalSignature lval binders typeAscriptionTk? type?
    -- Since `structInstFieldDecl` is a parser category and the kind of separation from the
    -- signature depends on the specific kind of `structInstFieldDecl`,
    -- `structInstFieldDecl` (unusually) manages its own leading whitespace.
    let structInstFieldDecl? ← fmt? structInstFieldDecl?
    if structInstFieldDecl?.isAlwaysEmpty then
      return signature
    let some structInstFieldDecl := getStructInstFieldDecl? structInstFieldDecl?
      | throw .partialFormatter
    return structInstFieldDecl.format signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeq1Indented]
public def fmtTacticSeq1Indented : Fmt := fun
  | `(Parser.Tactic.tacticSeq1Indented| $tactics:tactic;*) => do
    fmtSeq tactics none
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeqBracketed]
public def fmtTacticSeqBracketed : Fmt := fun
  | `(Parser.Tactic.tacticSeqBracketed|
      {%$lbTk
        $tactics:tactic;*
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let tactics ← fmtSeq tactics none
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk tactics rbTk <| .sparse hardNl
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.tacticSeq]
public def fmtTacticSeq : Fmt := fun
  | `(Parser.Tactic.tacticSeq| $tacticSeq:tacticSeq1Indented) =>
    fmt tacticSeq
  | `(Parser.Tactic.tacticSeq| $tacticSeq:tacticSeqBracketed) =>
    fmt tacticSeq
  | _ => throw .partialFormatter
