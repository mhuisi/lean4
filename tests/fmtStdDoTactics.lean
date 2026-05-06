import Std.Do
import Std.Tactic.Do
import Std.WP
import Std.WP.Triple.SpecLemmas

/-!
Tests for the formatters of the `Std.Tactic.Do` proof mode and verification condition generator
syntax: the `@[spec]` attribute (`fmtSpecAttr`), the proof mode tactics `mclear`, `mexact`,
`mpure`, `mrename_i`, `mspecialize`, `mspecialize_pure`, `mrefine`, `mintro`, `mrevert`,
`mexists`, `mdup`, `mhave`, `mreplace`, `mcases`, `mspec`, `mspec_no_bind` and `mspec_no_simp`,
the pattern categories `mcasesPat`, `mrefinePat`, `mintroPat` and `mrevertPat`, and the VC
generators `mvcgen`, `mvcgen?`, `vcgen` (both the tactic and the `grind` step) with their
`invariants`, `with`, `until`, `frames` and `simplifying_assumptions` clauses.

Every section contains forms that fit on one line, forms that exceed the 100 column soft width,
and forms with and without each optional component. A few `vcgen` examples exercise syntax that
the current implementation rejects (`with <tactic>`, `simplifying_assumptions <id>`) or cannot
discharge (`until`); they are kept because only their formatting matters here.
-/

set_option mvcgen.warning false
set_option grind.warning false
set_option warn.sorry false
set_option backward.do.legacy false

section ProofMode

open Std.Do

variable
  {σs : List Type}
  (P Q R : SPred σs)
  (φ ψ : Prop)

/-! ## `mintro`, `mexact`, `mclear` and `mpure` -/

theorem intro_exact : P ⊢ₛ P := by
  mstart
  mintro hp
  mexact hp

theorem intro_clear : P ⊢ₛ Q → Q := by
  mintro hp hq
  mclear hp
  mexact hq

theorem intro_tuple_pattern (accumulatorIsSorted accumulatorIsBounded : SPred σs) :
    accumulatorIsSorted ∧ accumulatorIsBounded ⊢ₛ accumulatorIsBounded := by
  mintro ⟨accumulatorIsSortedHypothesis, accumulatorIsBoundedHypothesis⟩
  mexact accumulatorIsBoundedHypothesis

theorem intro_forall (P Q R : SPred (Nat :: σs)) (h : ∀ n, P n ∧ Q n ⊢ₛ R n) : P ∧ Q ⊢ₛ R := by
  mintro ⟨hp, hq⟩ ∀state
  mstop
  exact h state

theorem intro_clear_pattern (hp : ⊢ₛ P) : Q ⊢ₛ P := by
  mintro -
  mexact hp

theorem pure_move (h : φ → ⊢ₛ Q) : ⌜φ⌝ ⊢ₛ Q := by
  mintro hφ
  mpure hφ
  mexact (h hφ)

theorem exact_long_witness (theAccumulatorIsSortedAndBoundedAndNonEmpty : SPred σs) :
    theAccumulatorIsSortedAndBoundedAndNonEmpty ⊢ₛ theAccumulatorIsSortedAndBoundedAndNonEmpty := by
  mintro theAccumulatorIsSortedAndBoundedAndNonEmptyHypothesis
  mexact theAccumulatorIsSortedAndBoundedAndNonEmptyHypothesis

/-! ## `mrename_i` -/

theorem rename_one : Q ⊢ₛ P → Q := by
  mintro _ _
  mrename_i hq _
  mexact hq

theorem rename_many (accumulatorIsSorted accumulatorIsBounded accumulatorIsNonEmpty : SPred σs) :
    accumulatorIsSorted ⊢ₛ accumulatorIsBounded → accumulatorIsNonEmpty → accumulatorIsSorted := by
  mintro _ _ _
  mrename_i theAccumulatorIsSorted theAccumulatorIsBounded theAccumulatorIsNonEmptyAndWellFormed
  mexact theAccumulatorIsSorted

/-! ## `mspecialize` and `mspecialize_pure` -/

theorem specialize_one : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mspecialize hpq hp
  mexact hpq

theorem specialize_many
    (theInitialAccumulator theSortedAccumulator theBoundedAccumulator : SPred σs) :
    theInitialAccumulator ⊢ₛ
      (theInitialAccumulator → theSortedAccumulator → theBoundedAccumulator) →
        theSortedAccumulator → theBoundedAccumulator := by
  mintro theInitialAccumulatorHolds theCombinedImplication theSortedAccumulatorHolds
  mspecialize theCombinedImplication theInitialAccumulatorHolds theSortedAccumulatorHolds
  mexact theCombinedImplication

theorem specialize_pure (y : Nat) (Ψ : Nat → SPred σs) (hp : ⊢ₛ P) (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) :
    ⊢ₛ Q → Ψ (y + 1) := by
  mintro hq
  mspecialize_pure (hΨ (y + 1)) hp hq => hΨApplied
  mexact hΨApplied

theorem specialize_pure_long (y : Nat) (Ψ : Nat → SPred σs) (hp : ⊢ₛ P)
    (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) : ⊢ₛ Q → Ψ (y + 1) := by
  mintro theQualifyingHypothesis
  mspecialize_pure (hΨ (y + 1)) hp theQualifyingHypothesis => theInstantiatedInvariantHypothesis
  mexact theInstantiatedInvariantHypothesis

/-! ## `mexists` -/

theorem exists_one (Ψ : Nat → SPred σs) : Ψ 42 ⊢ₛ ∃ x, Ψ x := by
  mintro h
  mexists 42

theorem exists_many (Ψ : Nat → Nat → Nat → SPred σs) : Ψ 1 2 3 ⊢ₛ ∃ x y z, Ψ x y z := by
  mintro h
  mexists 1, 2, 3

theorem exists_many_long (theWitnessRelation : Nat → Nat → Nat → Nat → SPred σs)
    (theInitialAccumulator : Nat) :
    theWitnessRelation (theInitialAccumulator + 1) (theInitialAccumulator + 2)
        (theInitialAccumulator + 3) (theInitialAccumulator + 4) ⊢ₛ
      ∃ x y z w, theWitnessRelation x y z w := by
  mintro h
  mexists theInitialAccumulator + 1, theInitialAccumulator + 2, theInitialAccumulator + 3,
    theInitialAccumulator + 4

/-! ## `mdup` -/

theorem dup_short : ⊢ₛ P → P := by
  mintro hp
  mdup hp => hp'
  mexact hp'

theorem dup_long (theAccumulatorInvariantHoldsAtEveryIteration : SPred σs) :
    ⊢ₛ theAccumulatorInvariantHoldsAtEveryIteration →
      theAccumulatorInvariantHoldsAtEveryIteration := by
  mintro theAccumulatorInvariantHoldsAtEveryIterationHypothesis
  mdup theAccumulatorInvariantHoldsAtEveryIterationHypothesis => theDuplicatedAccumulatorInvariant
  mexact theDuplicatedAccumulatorInvariant

/-! ## `mhave` and `mreplace` -/

theorem have_without_type : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mhave hq := by mspecialize hpq hp; mexact hpq
  mexact hq

theorem have_with_type : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mhave hq : Q := by mspecialize hpq hp; mexact hpq
  mexact hq

theorem replace_with_type : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mreplace hpq : Q := by mspecialize hpq hp; mexact hpq
  mexact hpq

theorem have_long_type (theAccumulatorIsSorted theAccumulatorIsBounded : SPred σs) :
    theAccumulatorIsSorted ⊢ₛ (theAccumulatorIsSorted → theAccumulatorIsBounded) →
      theAccumulatorIsBounded := by
  mintro theAccumulatorIsSortedHypothesis theSortednessImpliesBoundedness
  mhave theAccumulatorIsBoundednessWitness : theAccumulatorIsBounded := by
    mspecialize theSortednessImpliesBoundedness theAccumulatorIsSortedHypothesis
    mexact theSortednessImpliesBoundedness
  mexact theAccumulatorIsBoundednessWitness

end ProofMode

section CasesPatterns

open Std.Do

variable {σs : List Type} (P Q R : SPred σs) (φ ψ : Prop)

/-! ## `mcases` patterns -/

theorem cases_rename : P ⊢ₛ P := by
  mintro hp
  mcases hp with hp'
  mexact hp'

theorem cases_clear : ⊢ₛ P → Q → P := by
  mintro hp hq
  mcases hq with -
  mexact hp

theorem cases_pure (h : φ → ⊢ₛ R) : ⊢ₛ P → ⌜φ⌝ → R := by
  mintro hp hφ
  mcases hφ with ⌜hφPure⌝
  mexact h hφPure

theorem cases_pure_abbrev : (⌜φ⌝ ∧ ⌜ψ⌝) ⊢ₛ (⌜ψ⌝ : SPred σs) := by
  mintro h
  mcases h with ⟨%hφ, ⌜hψ⌝⟩
  mpure_intro
  exact hψ

theorem cases_tuple : (P ∧ Q ∧ R) ⊢ₛ R := by
  mintro h
  mcases h with ⟨hp, hq, hr⟩
  mexact hr

theorem cases_stateful : (P ∧ Q ∧ R) ⊢ₛ R := by
  mintro h
  mcases h with ⟨#hp, hq, □hr⟩
  mexact hr

theorem cases_alternatives : P ∧ (Q ∨ R) ∧ (Q → R) ⊢ₛ R := by
  mintro h
  mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩
  · mspecialize hqr hq
    mexact hqr
  · mexact hr

theorem cases_nested : P ∧ ((Q ∧ R) ∨ (R ∧ Q)) ⊢ₛ R := by
  mintro h
  mcases h with ⟨-, ⟨⟨hq, hr⟩ | ⟨hr, hq⟩⟩⟩
  · mexact hr
  · mexact hr

theorem cases_long_tuple
    (theAccumulatorIsSorted theAccumulatorIsBounded theAccumulatorIsNonEmpty : SPred σs)
    (theAccumulatorLengthsAgree : Prop) :
    (theAccumulatorIsSorted ∧ ⌜theAccumulatorLengthsAgree⌝ ∧ theAccumulatorIsBounded ∧
      theAccumulatorIsNonEmpty) ⊢ₛ theAccumulatorIsNonEmpty := by
  mintro theCombinedAccumulatorHypothesis
  mcases theCombinedAccumulatorHypothesis with
    ⟨theSortednessWitness, ⌜theLengthAgreementWitness⌝, □theBoundednessWitness,
      theNonEmptinessWitness⟩
  mexact theNonEmptinessWitness

theorem cases_long_alternatives
    (theAccumulatorIsSorted theAccumulatorIsBounded theAccumulatorIsNonEmpty : SPred σs) :
    (theAccumulatorIsSorted ∨ theAccumulatorIsBounded ∨ theAccumulatorIsNonEmpty) ⊢ₛ
      (theAccumulatorIsSorted ∨ theAccumulatorIsBounded ∨ theAccumulatorIsNonEmpty) := by
  mintro theCombinedAccumulatorHypothesis
  mcases theCombinedAccumulatorHypothesis with
    (theSortednessWitness | theBoundednessWitness | theNonEmptinessWitnessForTheAccumulator)
  · mleft
    mexact theSortednessWitness
  · mright
    mleft
    mexact theBoundednessWitness
  · mright
    mright
    mexact theNonEmptinessWitnessForTheAccumulator

end CasesPatterns

section RefinePatterns

open Std.Do

variable {σs : List Type} (P Q R : SPred σs)

/-! ## `mrefine` patterns -/

theorem refine_tuple : (P ∧ Q ∧ R) ⊢ₛ P ∧ R := by
  mintro ⟨hp, hq, hr⟩
  mrefine ⟨hp, hr⟩

theorem refine_pure (Ψ : Nat → SPred σs) : Ψ 42 ⊢ₛ ∃ x, Ψ x := by
  mintro h
  mrefine ⟨⌜42⌝, h⟩

theorem refine_pure_abbrev (Ψ : Nat → SPred σs) : Ψ 42 ⊢ₛ ∃ x, Ψ x := by
  mintro h
  mrefine ⟨%42, h⟩

theorem refine_stateful : (P ∧ Q) ⊢ₛ (P ∧ Q) := by
  mintro ⟨hp, hq⟩
  mrefine ⟨#hp, □hq⟩

theorem refine_hole : (P ∧ Q) ⊢ₛ (P ∧ Q) := by
  mintro ⟨hp, hq⟩
  mrefine ⟨?left, ?right⟩
  · mexact hp
  · mexact hq

theorem refine_parenthesized : P ⊢ₛ P := by
  mintro hp
  mrefine (hp)

theorem refine_long
    (theAccumulatorIsSorted theAccumulatorIsBounded theAccumulatorIsNonEmpty : SPred σs) :
    (theAccumulatorIsSorted ∧ theAccumulatorIsBounded ∧ theAccumulatorIsNonEmpty) ⊢ₛ
      (theAccumulatorIsSorted ∧ theAccumulatorIsBounded ∧ theAccumulatorIsNonEmpty) := by
  mintro ⟨theSortednessWitness, theBoundednessWitness, theNonEmptinessWitness⟩
  mrefine ⟨#theSortednessWitness, □theBoundednessWitness, (theNonEmptinessWitness)⟩

end RefinePatterns

section RevertPatterns

open Std.Do

variable {σs : List Type} (P Q R : SPred σs)

/-! ## `mrevert` patterns -/

theorem revert_one : (P ∧ Q) ⊢ₛ P := by
  mintro ⟨hp, hq⟩
  mrevert hq
  mintro hq'
  mexact hp

theorem revert_forall (Ψ : Nat → SPred (Nat :: σs)) : (∀ x, Ψ x) ⊢ₛ (∀ x, Ψ x) := by
  mintro h ∀n
  mrevert ∀1
  mstop
  sorry

theorem revert_forall_without_index (Ψ : Nat → SPred (Nat :: σs)) : (∀ x, Ψ x) ⊢ₛ (∀ x, Ψ x) := by
  mintro h ∀n
  mrevert ∀
  mstop
  sorry

theorem revert_many
    (theAccumulatorIsSorted theAccumulatorIsBounded theAccumulatorIsNonEmpty : SPred σs) :
    (theAccumulatorIsSorted ∧ theAccumulatorIsBounded ∧ theAccumulatorIsNonEmpty) ⊢ₛ
      theAccumulatorIsNonEmpty := by
  mintro ⟨theSortednessWitness, theBoundednessWitness, theNonEmptinessWitness⟩
  mrevert theSortednessWitness theBoundednessWitness theNonEmptinessWitness
  mintro theRevertedSortedness theRevertedBoundedness theRevertedNonEmptiness
  massumption

end RevertPatterns

section Programs

/-- Sum up all numbers below `n`. -/
def sumBelow (n : Nat) : Id Nat := do
  let mut accumulator := 0
  for i in [0:n] do
    accumulator := accumulator + i
  return accumulator

/-- Check that every number below `n` satisfies `p`. -/
def checkAllBelow (p : Nat → Prop) [DecidablePred p] (n : Nat) : Bool := Id.run do
  for i in [0:n] do
    if ¬ p i then
      return false
  return true

/-- Read the counter and bump it by one. -/
def readAndBump : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  return n

/-- Bump the counter by `delta`. -/
def bumpBy (delta : Nat) : StateM Nat Unit :=
  modify (· + delta)

/-- Read the counter, then bump it by `delta` on top of the implicit bump of `readAndBump`. -/
def readAndBumpBy (delta : Nat) : StateM Nat Nat := do
  let n ← readAndBump
  bumpBy delta
  return n

end Programs

section Spec

open Std.Do

/-! ## The `@[spec]` attribute -/

@[spec]
theorem readAndBump_spec (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mvcgen [readAndBump]
  simp_all

@[spec 500]
theorem readAndBump_spec_with_priority (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ :=
  readAndBump_spec k

attribute [local spec 1000] readAndBump_spec_with_priority

/-! ## `mspec`, `mspec_no_bind` and `mspec_no_simp` -/

theorem spec_without_argument (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mintro _
  mspec

theorem spec_with_argument (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mintro _
  mspec readAndBump_spec k

theorem spec_no_simp (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mintro _
  mspec_no_simp readAndBump_spec k

theorem spec_no_bind (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mintro _
  mspec_no_bind

theorem spec_with_long_argument (theInitialValueOfTheCounter : Nat) :
    ⦃fun s => ⌜s = theInitialValueOfTheCounter⌝⦄ readAndBump
      ⦃⇓ r s => ⌜r = theInitialValueOfTheCounter ∧ s = theInitialValueOfTheCounter + 1⌝⦄ := by
  mintro _
  mspec_no_bind readAndBump_spec_with_priority theInitialValueOfTheCounter

end Spec

section MVCGen

open Std.Do

/-! ## `mvcgen` and `mvcgen?` -/

theorem mvcgen_bare (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mvcgen

theorem mvcgen_with_config_and_lemmas (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mvcgen (leave := false) [readAndBump, -readAndBump_spec, *]

theorem mvcgen_dot_invariants (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ checkAllBelow p n := by
  generalize h : checkAllBelow p n = x
  apply Id.of_wp_run_eq h
  mvcgen [checkAllBelow] invariants
    · Invariant.withEarlyReturnNewDo
        (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
        (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]
  all_goals sorry

theorem mvcgen_named_invariants_and_vc_alternatives (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ checkAllBelow p n := by
  generalize h : checkAllBelow p n = x
  apply Id.of_wp_run_eq h
  mvcgen [checkAllBelow] invariants
    | inv1 => Invariant.withEarlyReturnNewDo
        (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
        (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
    with
    | vc1 | vc2 => simp_all [-Classical.not_forall]; try grind
    | vc3 => simp_all [-Classical.not_forall]; try grind
  all_goals simp_all [-Classical.not_forall]
  all_goals sorry

theorem mvcgen_shared_discharger (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mvcgen [readAndBump] with simp_all

theorem mvcgen_hint (k : Nat) :
    ⦃fun s => ⌜s = k⌝⦄ readAndBump ⦃⇓ r s => ⌜r = k ∧ s = k + 1⌝⦄ := by
  mvcgen?
  sorry

theorem mvcgen_hint_with_long_argument_list (theInitialValueOfTheCounter : Nat) :
    ⦃fun s => ⌜s = theInitialValueOfTheCounter⌝⦄ readAndBump
      ⦃⇓ r s => ⌜r = theInitialValueOfTheCounter ∧ s = theInitialValueOfTheCounter + 1⌝⦄ := by
  mvcgen? (elimLets := false) (stepLimit := some 42) [readAndBump, readAndBump_spec,
    readAndBump_spec_with_priority]
  sorry

end MVCGen

section VCGen

open Std.WP
open Lean.Order

/-! ## `vcgen` -/

theorem vcgen_bare (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] invariants
  | inv1 => fun _ _ => True
  with finish

theorem vcgen_with_config (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen (errorOnMissingSpec := false) [sumBelow]
  all_goals sorry

theorem vcgen_until (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] until (sumBelow n)
  all_goals sorry

theorem vcgen_frames (delta : Nat) : ⦃ fun _ => True ⦄ readAndBumpBy delta ⦃ fun _ _ => True ⦄ := by
  vcgen [readAndBumpBy, readAndBump, bumpBy] frames
  | readAndBump => fun _ => True
  all_goals sorry

theorem vcgen_many_frames (theDeltaAppliedToTheCounter : Nat) :
    ⦃ fun _ => True ⦄ readAndBumpBy theDeltaAppliedToTheCounter ⦃ fun _ _ => True ⦄ := by
  vcgen [readAndBumpBy, readAndBump, bumpBy] frames
  | readAndBump => fun _ => True
  | bumpBy theDeltaAppliedToTheCounterByThisCall => fun _ => True
  all_goals sorry

theorem vcgen_dot_invariants (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] invariants
  · fun _ _ => True
  with finish

theorem vcgen_simplifying_assumptions (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] invariants
  | inv1 => fun _ _ => True
  simplifying_assumptions [Nat.add_assoc]
  with finish

-- The named `simplifying_assumptions <id>` form parses, but `vcgen` does not support named
-- `Sym.simp` variants yet and rejects it during elaboration.
theorem vcgen_named_simplifying_assumptions (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] invariants
  | inv1 => fun _ _ => True
  simplifying_assumptions theAssumptionSet [Nat.add_assoc, Nat.add_comm]
  with finish

-- `with <tactic>` is the low-priority catch-all alternative of `vcgenDischarge`, taken here
-- because `grind` is a tactic rather than a `grind`-mode step; the elaborator rejects it with a
-- dedicated error message instead of a raw parser error.
theorem vcgen_with_plain_tactic (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] invariants
  | inv1 => fun _ _ => True
  with grind

-- `until <term>` must be the last clause before `with`: the term parser would otherwise swallow
-- the non-reserved `frames`/`invariants`/`simplifying_assumptions` keyword as an argument.
theorem vcgen_until_with (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  vcgen [sumBelow] until (sumBelow n) with finish
  all_goals sorry

theorem vcgen_everything (theDeltaAppliedToTheCounter : Nat) :
    ⦃ fun _ => True ⦄ readAndBumpBy theDeltaAppliedToTheCounter ⦃ fun _ _ => True ⦄ := by
  vcgen (elimLets := false) (stepLimit := some 42) [readAndBumpBy, readAndBump, bumpBy]
    frames
    | readAndBump => fun _ => True
    | bumpBy theDeltaAppliedToTheCounterByThisParticularCall => fun _ => True
    simplifying_assumptions [Nat.add_assoc, Nat.add_comm, Nat.mul_comm]
    with finish
  all_goals sorry

/-! ## `vcgen` as a `grind` step -/

theorem grind_vcgen_bare (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  sym =>
    vcgen [sumBelow] invariants
    | inv1 => fun _ _ => True
    finish

theorem grind_vcgen_with_config (n : Nat) : ⦃ True ⦄ sumBelow n ⦃ fun _ => True ⦄ := by
  sym =>
    vcgen (errorOnMissingSpec := false) [sumBelow] invariants
    | inv1 => fun _ _ => True
    finish

theorem grind_vcgen_everything (theUpperBoundOfTheSummation : Nat) :
    ⦃ True ⦄ sumBelow theUpperBoundOfTheSummation ⦃ fun _ => True ⦄ := by
  sym =>
    vcgen (elimLets := false) [sumBelow, checkAllBelow, readAndBump]
      invariants
      | inv1 => fun _ _ => True
      simplifying_assumptions [Nat.add_assoc, Nat.add_comm]
    finish

end VCGen
