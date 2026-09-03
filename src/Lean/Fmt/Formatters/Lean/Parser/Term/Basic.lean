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
deriving BEq, Inhabited, Repr, Hashable

private def BinderKind.classify (binder : TSyntax binderKinds) : BinderKind :=
  match binder.raw with
  | `(explicitBinderF| ($ids* $[: $type?:term]? $[$default?]?)) =>
    c ids .explicit
  | `(implicitBinderF| {$ids* $[: $type?:term]?})
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
    c ids .implicit
  | `(Parser.Term.instBinder| [$[$_ :]? $_]) => .instance
  | _ =>
    -- `ident` and `hole` binders
    c #[binder] .explicit
where
  c (ids : Array Syntax) (k : BinderKind) : BinderKind :=
    if ids.all (·.getKind == ``Parser.Term.hole) then
      .instance
    else
      k

private structure BinderWithDependents where
  idx : Nat
  kind : BinderKind
  binder : TSyntax binderKinds
  type? : Option Syntax
  default? : Option Syntax
  dependents : Array (Std.HashSet Nat)
deriving BEq, Inhabited

private def splitBinder (binder : TSyntax binderKinds) : Array Name × Option Syntax × Option Syntax :=
  if binder.raw.isIdent then
    (#[binder.raw.getId], none, none)
  else
    match binder.raw with
    | `(explicitBinderF| ($ids* $[: $type?:term]? $[$default?]?)) =>
      (binderIdentNames ids, type?.map (·.raw), default?.map (·.raw))
    | `(implicitBinderF| {$ids* $[: $type?:term]?})
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
      (binderIdentNames ids, type?.map (·.raw), none)
    | `(Parser.Term.instBinder| [$[$id?:ident :]? $classType:term]) =>
      (id?.toArray.map (·.getId), some classType.raw, none)
    | _ =>
      (#[], none, none)
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
    let (boundVars, type?, default?) := splitBinders[i]!
    let mut dependents := #[]
    for bv in boundVars do
      let mut bvDependents := {}
      for j in (i + 1)...binders.size do
        let (_, body?, _) := splitBinders[j]!
        if body?.any (referencesVar bv) then
          bvDependents := bvDependents.insert j
      dependents := dependents.push bvDependents
    result := result.push ⟨i, .classify binders[i]!, binders[i]!, type?, default?, dependents⟩
  return result

private def hashPreresolved : Syntax.Preresolved → UInt64
  | .namespace ns => mixHash 11 (hash ns)
  | .decl n fields => mixHash 13 (mixHash (hash n) (hash fields))

/-- Hashes the same fields that `Syntax.structEq` compares, so it is consistent with `BEq Syntax`. -/
private partial def hashSyntax : Syntax → UInt64
  | .missing => 17
  | .node _ k args => args.foldl (fun r a => mixHash r (hashSyntax a)) (mixHash 19 (hash k))
  | .atom _ val => mixHash 23 (hash val)
  | .ident _ rawVal val preresolved =>
    let h := mixHash 29 (hash rawVal.repair.toString)
    let h := mixHash h (hash val)
    preresolved.foldl (fun r p => mixHash r (hashPreresolved p)) h

private instance : Hashable Syntax := ⟨hashSyntax⟩

private structure PendingBinderGroup where
  binders : Array BinderWithDependents
  kinds : Std.HashSet BinderKind
  dependents : Std.HashSet Nat
  defaultKinds : Std.HashSet Bool
  types : Std.HashSet Syntax
  deriving Inhabited

private def PendingBinderGroup.init (b : BinderWithDependents) : PendingBinderGroup := {
  binders := #[b]
  kinds := {b.kind}
  dependents := b.dependents.foldr Std.HashSet.union {}
  defaultKinds := {b.default?.isSome}
  types := b.type?.map ({·}) |>.getD {}
}

private def PendingBinderGroup.merge (g1 g2 : PendingBinderGroup) : PendingBinderGroup := {
  binders := g1.binders ++ g2.binders
  kinds := g1.kinds.union g2.kinds
  dependents := g1.dependents.union g2.dependents
  defaultKinds := g1.defaultKinds.union g2.defaultKinds
  types := g1.types.union g2.types
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
  let runs := computeKindRuns binders |>.map (·.map PendingBinderGroup.init)
  let runs := runs.map groupAdjacentImplicitsAndInstances
  let binderToGroup : Std.HashMap Nat Nat :=
    runs.flatMap id |>.mapIdx (fun groupIdx group => group.binders.map (·.idx, groupIdx))
      |>.flatMap id
      |> Std.HashMap.ofArray
  let runs := runs.map fun run => Id.run do
    let mut groups := run
    groups := groupAdjacentExplicitsBySameGroupDependents binderToGroup groups
    groups := groupAdjacentByDependencies groups
    groups := groupAdjacentBinderlessExplicits groups
    groups := groupAdjacentExplicitsBySameType groups
    groups := groupAdjacentExplicitsWithoutDependents groups
    return groups.map (·.binders)
  let runs := runs.map divideIntoSubgroups
  return runs.flatMap (·.map (·.map (·.map (·.binder))))
where
  computeKindRuns (binders : Array BinderWithDependents) : Array (Array BinderWithDependents) := Id.run do
    let mut kindRuns := #[]
    let mut activeRun := #[binders[0]!]
    for b in binders[1...*] do
      match activeRun.back!.kind, b.kind with
      | .implicit, .implicit
      | .implicit, .explicit
      | .implicit, .instance
      | .explicit, .explicit
      | .explicit, .instance
      | .instance, .instance =>
        activeRun := activeRun.push b
      | _, _ =>
        kindRuns := kindRuns.push activeRun
        activeRun := #[b]
    kindRuns := kindRuns.push activeRun
    return kindRuns
  groupAdjacentImplicitsAndInstances (groups : Array PendingBinderGroup) : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isImplicitsOrInstances := ! activeGroup.kinds.contains .explicit && ! g.kinds.contains .explicit
      if isImplicitsOrInstances then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsBySameGroupDependents (binderToGroup : Std.HashMap Nat Nat) (groups : Array PendingBinderGroup) : Array PendingBinderGroup := Id.run do
    let groupDependents (g : PendingBinderGroup) : Std.HashSet Nat :=
      g.dependents.toArray.map binderToGroup.get! |> Std.HashSet.ofArray
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    let mut activeGroupGroupDependents : Std.HashSet Nat := groupDependents groups[0]!
    for g in groups[1...*] do
      let gGroupDependents := groupDependents g
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      if isExplicits && ! activeGroupGroupDependents.isEmpty && ! gGroupDependents.isEmpty && activeGroupGroupDependents == gGroupDependents then
        activeGroup := activeGroup.merge g
        activeGroupGroupDependents := activeGroupGroupDependents.union gGroupDependents
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
        activeGroupGroupDependents := gGroupDependents
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentByDependencies (groups : Array PendingBinderGroup)  : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      if g.binders.all (activeGroup.dependents.contains ·.idx) then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentBinderlessExplicits (groups : Array PendingBinderGroup)  : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      let isBinderless := activeGroup.types.isEmpty && g.types.isEmpty
      if isExplicits && isBinderless && activeGroup.defaultKinds == g.defaultKinds then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsBySameType (groups : Array PendingBinderGroup) : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      let sameType : Bool := activeGroup.types.size == 1 && activeGroup.types == g.types
      if isExplicits && sameType && activeGroup.defaultKinds == g.defaultKinds then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsWithoutDependents (groups : Array PendingBinderGroup)  : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      if isExplicits && activeGroup.dependents.isEmpty && g.dependents.isEmpty && activeGroup.defaultKinds == g.defaultKinds then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  divideIntoSubgroups (groups : Array (Array BinderWithDependents)) : Array (Array (Array BinderWithDependents)) :=
    groups.map fun group => Id.run do
      let mut dividedGroups : Array (Array BinderWithDependents) := #[]
      let mut activeGroup : Array BinderWithDependents := #[group[0]!]
      for b in group[1...*] do
        match activeGroup.back!.kind, b.kind with
        | .implicit, .implicit
        | .instance, .instance =>
          activeGroup := activeGroup.push b
        | .explicit, .explicit =>
          if activeGroup.back!.default?.isSome == b.default?.isSome then
            activeGroup := activeGroup.push b
          else
            dividedGroups := dividedGroups.push activeGroup
            activeGroup := #[b]
        | _, _ =>
          dividedGroups := dividedGroups.push activeGroup
          activeGroup := #[b]
      dividedGroups := dividedGroups.push activeGroup
      return dividedGroups
  isDefaultEquivalent (group1 group2 : Array BinderWithDependents) : Bool :=
    let defaults1 := Std.HashSet.ofArray <| group1.map (·.default?.isSome)
    let defaults2 := Std.HashSet.ofArray <| group2.map (·.default?.isSome)
    defaults1 == defaults2

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
