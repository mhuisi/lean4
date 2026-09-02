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
  | explicit (isBinderIdent : Bool)
  | implicit (isBinderIdent : Bool)
  | instance (isBinderIdent : Bool)
deriving BEq, Inhabited, Repr

private def BinderKind.classify (binder : TSyntax binderKinds) : BinderKind :=
  match binder.raw with
  | `(explicitBinderF| ($ids* $[: $type?:term]? $[$default?]?)) =>
    c ids <| .explicit (isBinderIdent := type?.isNone && default?.isNone)
  | `(implicitBinderF| {$ids* $[: $type?:term]?})
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
    c ids <| .implicit (isBinderIdent := type?.isNone)
  | `(Parser.Term.instBinder| [$[$_ :]? $_]) => .instance (isBinderIdent := false)
  | _ =>
    -- `ident` and `hole` binders
    c #[binder] <| .explicit (isBinderIdent := true)
where
  c (ids : Array Syntax) (k : BinderKind) : BinderKind :=
    if ids.all (·.getKind == ``Parser.Term.hole) then
      .instance (isBinderIdent := false)
    else
      k

private structure BinderWithDependents where
  idx : Nat
  kind : BinderKind
  binder : TSyntax binderKinds
  dependents : Array (Std.HashSet Nat)
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
    | `(explicitBinderF| ($ids* $[: $type?:term]? $[$_]?)) =>
      (binderIdentNames ids, type?.toArray.map (·.raw))
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

private partial def referencesVar (var : Name) : Syntax → Bool
  | .ident _ _ id _ => var.isPrefixOf id
  | .node _ _ args  => args.any (referencesVar var)
  | _               => false

private def computeBinderDependents
    (binders : TSyntaxArray binderKinds)
    : Array BinderWithDependents := Id.run do
  let splitBinders := binders.map splitBinder
  let mut result := Array.emptyWithCapacity binders.size
  for i in 0...binders.size do
    let (boundVars, _) := splitBinders[i]!
    let mut dependents := #[]
    for bv in boundVars do
      let mut bvDependents := {}
      for j in (i + 1)...binders.size do
        let (_, body) := splitBinders[j]!
        if body.any (referencesVar bv) then
          bvDependents := bvDependents.insert j
      dependents := dependents.push bvDependents
    result := result.push ⟨i, .classify binders[i]!, binders[i]!, dependents⟩
  return result

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
  let mut runs := computeKindRuns binders |>.map fun run => run.map (#[·])
  for i in (0...runs.size) do
    runs := runs.modify i fun run => Id.run do
      let mut groups := run
      groups := groupAdjacentImplicitsAndInstances groups
      groups := groupAdjacentExplicitsBySameDependents groups
      groups := groupAdjacentByDependencies groups
      groups := groupAdjacentBinderlessExplicits groups
      groups := groupAdjacentExplicitsWithoutDependents groups
      return groups
  let runs' := runs.map divideIntoKindSubgroups
  return runs'.flatMap (·.map (·.map (·.map (·.binder))))
where
  computeKindRuns (binders : Array BinderWithDependents) : Array (Array BinderWithDependents) := Id.run do
    let mut kindRuns := #[]
    let mut activeRun := #[binders[0]!]
    for b in binders[1...*] do
      match activeRun.back!.kind, b.kind with
      | .implicit .., .implicit ..
      | .implicit .., .explicit ..
      | .implicit .., .instance ..
      | .explicit .., .explicit ..
      | .explicit .., .instance ..
      | .instance .., .instance .. =>
        activeRun := activeRun.push b
      | _, _ =>
        kindRuns := kindRuns.push activeRun
        activeRun := #[b]
    kindRuns := kindRuns.push activeRun
    return kindRuns
  groupAdjacentImplicitsAndInstances (groups : Array (Array BinderWithDependents)) : Array (Array BinderWithDependents) := Id.run do
    let mut groupedGroups : Array (Array BinderWithDependents) := #[]
    let mut activeGroup : Array BinderWithDependents := groups[0]!
    for g in groups[1...*] do
      let isImplicitsOrInstances :=
        activeGroup.all (fun b => b.kind matches .implicit ..)
            && g.all (fun b => b.kind matches .implicit .. || b.kind matches .instance ..)
          || activeGroup.all (fun b => b.kind matches .implicit .. || b.kind matches .instance ..)
            && g.all (fun b => b.kind matches .instance ..)
      if isImplicitsOrInstances then
        activeGroup := activeGroup ++ g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsBySameDependents (groups : Array (Array BinderWithDependents)) : Array (Array BinderWithDependents) := Id.run do
    let mut groupedGroups : Array (Array BinderWithDependents) := #[]
    let mut activeGroup : Array BinderWithDependents := groups[0]!
    for g in groups[1...*] do
      let activeGroupDependents := activeGroup.flatMap (·.dependents) |>.foldr Std.HashSet.union {} |>.toArray.map (fun i => groups.findIdx (fun g => g.any (·.idx == i))) |> Std.HashSet.ofArray
      let gDependents := g.flatMap (·.dependents) |>.foldr Std.HashSet.union {} |>.toArray.map (fun i => groups.findIdx (fun g => g.any (·.idx == i))) |> Std.HashSet.ofArray
      let isExplicits := activeGroup.all (·.kind matches .explicit ..) && g.all (·.kind matches .explicit ..)
      if isExplicits && ! activeGroupDependents.isEmpty && ! gDependents.isEmpty && activeGroupDependents == gDependents then
        activeGroup := activeGroup ++ g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentByDependencies (groups : Array (Array BinderWithDependents))  : Array (Array BinderWithDependents) := Id.run do
    let mut groupedGroups : Array (Array BinderWithDependents) := #[]
    let mut activeGroup : Array BinderWithDependents := groups[0]!
    for g in groups[1...*] do
      if g.all (fun b => activeGroup.any (·.dependents.any (·.contains b.idx))) then
        activeGroup := activeGroup ++ g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsWithoutDependents (groups : Array (Array BinderWithDependents))  : Array (Array BinderWithDependents) := Id.run do
    let mut groupedGroups : Array (Array BinderWithDependents) := #[]
    let mut activeGroup : Array BinderWithDependents := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.all (·.kind matches .explicit ..) && g.all (·.kind matches .explicit ..)
      if isExplicits && activeGroup.all (·.dependents.all (·.isEmpty)) && g.all (·.dependents.all (·.isEmpty)) then
        activeGroup := activeGroup ++ g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentBinderlessExplicits (groups : Array (Array BinderWithDependents))  : Array (Array BinderWithDependents) := Id.run do
    let mut groupedGroups : Array (Array BinderWithDependents) := #[]
    let mut activeGroup : Array BinderWithDependents := groups[0]!
    for g in groups[1...*] do
      let isBinderlessExplicits := activeGroup.all (·.kind matches .explicit true) && g.all (·.kind matches .explicit true)
      if isBinderlessExplicits then
        activeGroup := activeGroup ++ g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  divideIntoKindSubgroups (groups : Array (Array BinderWithDependents)) : Array (Array (Array BinderWithDependents)) :=
    groups.map fun group => Id.run do
      let mut dividedGroups : Array (Array BinderWithDependents) := #[]
      let mut activeGroup : Array BinderWithDependents := #[group[0]!]
      for b in group[1...*] do
        match activeGroup.back!.kind, b.kind with
        | .implicit .., .implicit ..
        | .explicit .., .explicit ..
        | .instance .., .instance .. =>
          activeGroup := activeGroup.push b
        | _, _ =>
          dividedGroups := dividedGroups.push activeGroup
          activeGroup := #[b]
      dividedGroups := dividedGroups.push activeGroup
      return dividedGroups

public def fmtBinders
    (binders : TSyntaxArray binderKinds)
    : FmtM (Array (Array (Array TaggedDoc))) := do
  let binderGroups := groupBinders binders
  let binderGroups ← binderGroups.mapM fun binderGroup => binderGroup.mapM fun subBinderGroup => subBinderGroup.mapM fmt
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
