import Std.Do
import Std.Internal.Do.ExceptPost
import Std.Internal.Do.Order.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Entails

/-!
Tests for the formatters of the `Std.Do` program logic notations: `wp⟦_⟧` and `wp⟦_ : _⟧`
(`fmtWP`), `⌜_⌝` (`fmtSPredPure`), `⊢ₛ _` (`fmtSPredTautology`), `_ ⊣⊢ₛ _` (`fmtSPredBientails`),
`spred(_)` and `term(_)` (`fmtSPred`, `fmtSPredTermEscape`), `post⟨_⟩` (`fmtPostCond`),
`⇓ _ => _` and `⇓? _ => _` (`fmtNoThrowPostCond`, `fmtMayThrowPostCond`), `EPost⟨_⟩` and
`epost⟨_⟩` (`fmtEPostType`, `fmtEPostValue`), the complete lattice notations `⌜_⌝`, `⨅ _, _` and
`⨆ _, _` (`fmtLatticeOfProp`, `fmtIInf`, `fmtISup`), and `_ ⊭ _` (`fmtNotEntails`).

Every section contains forms that fit on one line, forms that exceed the 100 column soft width,
and forms with and without each optional component.
-/

section SPred

open Std.Do

variable
  {σs : List Type}
  (P Q R : SPred σs)
  (xs ys zs : List Nat)
  (n m : Nat)
  (isBalanced isSortedAscending : List Nat → Prop)

/-! ## `⌜_⌝` -/

example : SPred σs := ⌜n = m⌝

example : SPred σs := ⌜xs.length = ys.length ∧ isBalanced xs⌝

example : SPred σs :=
  ⌜xs.length = ys.length ∧ isSortedAscending xs ∧ isSortedAscending ys ∧ xs.Perm ys ∧ zs = []⌝

example : SPred σs :=
  ⌜xs.length = ys.length ∧ isSortedAscending xs ∧ isSortedAscending ys ∧ xs.Perm ys ∧
    isBalanced zs ∧ zs.length = xs.length + ys.length⌝

example : SPred σs := ⌜∀ i, i < xs.length → xs[i]! ≤ xs[i + 1]!⌝

/-! ## `⊢ₛ _` and `_ ⊣⊢ₛ _` -/

example : Prop := ⊢ₛ P

example : Prop := ⊢ₛ (⌜n = m⌝ : SPred σs)

example : Prop := ⊢ₛ SPred.and P (SPred.or Q R)

example : Prop :=
  ⊢ₛ SPred.imp P ⌜xs.length = ys.length ∧ isSortedAscending xs ∧ isSortedAscending ys ∧ zs = []⌝

example : Prop := P ⊣⊢ₛ Q

example : Prop := SPred.and P Q ⊣⊢ₛ SPred.and Q P

example : Prop :=
  SPred.and (SPred.or P Q) (SPred.or P R) ⊣⊢ₛ SPred.or P (SPred.and Q R)

example : Prop :=
  ⌜xs.length = ys.length ∧ isBalanced xs⌝ ⊣⊢ₛ
    SPred.and ⌜xs.length = ys.length⌝ (⌜isBalanced xs⌝ : SPred σs)

/-! ## `spred(_)` and `term(_)` -/

example : SPred σs := spred(P ∧ Q)

example : SPred σs := spred(¬P ∨ (Q → R))

example : SPred σs := spred(∀ i, ⌜i < xs.length⌝ → ⌜xs[i]! ≤ n⌝)

example : SPred σs :=
  spred(∃ i, ⌜i < xs.length ∧ xs[i]! = n⌝ ∧ ∀ j, ⌜j < i⌝ → ⌜xs[j]! ≠ n⌝)

example : SPred σs :=
  spred((P ∧ Q) ∨ (P ∧ R) ∨ (Q ∧ R) ∨ ⌜isBalanced xs ∧ isSortedAscending ys ∧ xs.length = n⌝)

example : SPred σs := spred(term(SPred.and P Q))

example : SPred σs :=
  spred(P ∧ term(if n = m then SPred.and Q R else SPred.or Q R) ∧ ⌜isBalanced xs⌝)

end SPred

section PostCond

open Std.Do

variable
  {ps : PostShape}
  (successCondition : Nat → Assertion (.arg Nat .pure))
  (xs : List Nat)
  (n : Nat)

/-! ## `post⟨_⟩` -/

example : PostCond Nat (.arg Nat .pure) := post⟨successCondition⟩

example : PostCond Nat .pure := post⟨fun r => ⌜r = 0⌝⟩

example : PostCond Nat (.except String .pure) :=
  post⟨fun r => ⌜r = xs.length⌝, fun e => ⌜e = "out of bounds"⌝⟩

example : PostCond Nat (.except String (.except Unit .pure)) :=
  post⟨fun r => ⌜r = xs.length ∧ xs ≠ []⌝, fun e => ⌜e = "out of bounds"⌝, fun _ => ⌜True⌝⟩

example : PostCond Nat (.except String (.except Unit .pure)) :=
  post⟨
    fun r => ⌜r = xs.length ∧ xs ≠ [] ∧ ∀ i, i < xs.length → xs[i]! ≤ n⌝,
    fun e => ⌜e = "index out of bounds while traversing the input list"⌝,
    fun _ => ⌜True⌝
  ⟩

/-! ## `⇓ _ => _` and `⇓? _ => _` -/

example : PostCond Nat ps := ⇓r => ⌜r = n⌝

example : PostCond Nat (.arg Nat .pure) := ⇓ r s => ⌜r = n ∧ s = xs.length⌝

example : PostCond (Nat × Nat) ps := ⇓ ⟨lo, hi⟩ => ⌜lo ≤ hi⌝

example : PostCond Nat ps := ⇓ _ => ⌜True⌝

example : PostCond Nat (.arg Nat .pure) :=
  ⇓ r s => ⌜r = xs.length ∧ s = n ∧ ∀ i, i < xs.length → xs[i]! ≤ r ∧ xs[i]! ≤ s ∧ r ≤ n⌝

example : PostCond Nat ps := ⇓?r => ⌜r = n⌝

example : PostCond Nat (.arg Nat .pure) := ⇓? r s => ⌜r = n ∧ s = xs.length⌝

example : PostCond Nat (.arg Nat .pure) :=
  ⇓? r s => ⌜r = xs.length ∧ s = n ∧ ∀ i, i < xs.length → xs[i]! ≤ r ∧ xs[i]! ≤ s ∧ r ≤ n⌝

end PostCond

section WP

open Std.Do

abbrev Counter := StateM Nat

def increment : Counter Nat := do
  let n ← get
  set (n + 1)
  return n

def incrementTwice : Counter Nat := do
  let _ ← increment
  increment

/-! ## `wp⟦_⟧` and `wp⟦_ : _⟧` -/

example : Assertion (.arg Nat .pure) := wp⟦increment⟧ (⇓ r s => ⌜r + 1 = s⌝)

example : Assertion (.arg Nat .pure) := wp⟦increment : Counter Nat⟧ (⇓ r s => ⌜r + 1 = s⌝)

example : Prop := ⊢ₛ wp⟦incrementTwice⟧ (⇓ r s => ⌜r + 2 = s⌝)

example : Prop :=
  ⊢ₛ wp⟦incrementTwice⟧ (⇓ r s => ⌜r + 2 = s ∧ s ≥ 2 ∧ (∀ k, k ≤ r → k ≤ s) ∧ r ≤ s⌝)

example : Prop :=
  ⊢ₛ wp⟦do
      let n ← increment
      let m ← increment
      return n + m⟧ (⇓ r s => ⌜r + 3 = 2 * s⌝)

example : Prop :=
  ⊢ₛ wp⟦(do
        let firstReading ← increment
        let secondReading ← increment
        return firstReading + secondReading) :
      Counter Nat⟧ (⇓ r s => ⌜r + 3 = 2 * s⌝)

end WP

section ExceptPost

open Std.Internal.Do
open Lean.Order

variable (l : Type) [CompleteLattice l] (handleIO handleUser : String → l)

/-! ## `EPost⟨_⟩` and `epost⟨_⟩` -/

example : Type := EPost⟨⟩

example : Type := EPost⟨String → l⟩

example : Type := EPost⟨String → l, Unit → l⟩

example : Type :=
  EPost⟨String → EPost.Cons (Unit → l) EPost.Nil, Unit → l, Nat → EPost.Cons (String → l) EPost.Nil⟩

example : Type :=
  EPost⟨
    String → EPost.Cons (Unit → l) EPost.Nil,
    Unit → EPost.Cons (String → l) (EPost.Cons (Unit → l) EPost.Nil),
    Nat → EPost.Cons (String → l) EPost.Nil
  ⟩

example : EPost.Nil := epost⟨⟩

example : EPost.Cons (String → l) EPost.Nil := epost⟨handleIO⟩

example : EPost.Cons (String → l) (EPost.Cons (String → l) EPost.Nil) :=
  epost⟨handleIO, handleUser⟩

example : EPost.Cons (String → l) (EPost.Cons (String → l) (EPost.Cons (String → l) EPost.Nil)) :=
  epost⟨fun message => handleIO message, fun message => handleUser message, fun _ => handleIO ""⟩

end ExceptPost

noncomputable section CompleteLattice

open Lean.Order

variable
  {α : Type}
  [CompleteLattice α]
  (f g : Nat → α)
  (h : Nat → Nat → α)
  (approximate : Nat → Nat → Nat → α)
  (p q : Prop)

/-! ## `⌜_⌝` for complete lattices -/

example : α := ⌜p⌝

example : α := ⌜p ∧ q⌝

example : α := ⌜∀ i j : Nat, i ≤ j → f i ⊑ f j ∧ g i ⊑ g j ∧ h i j ⊑ h j i ∧ i + j ≤ i * j + 1⌝

/-! ## `⨅ _, _` and `⨆ _, _` -/

example : α := ⨅ i, f i

example : α := ⨆ i, f i

example : α := ⨅ (i : Nat), f i ⊔ g i

example : α := ⨆ i j, h i j

example : α := ⨅ i, ⨆ j, h i j

example : α := ⨆ i, ⨅ j, ⨆ k, approximate i j k

example : α :=
  ⨅ i, ⨆ j, approximate i j 0 ⊔ approximate i j 1 ⊔ approximate i j 2 ⊔ approximate i j 3 ⊔ f i

example : α :=
  ⨆ iterationIndex, ⨅ approximationDepth,
    approximate iterationIndex approximationDepth 0 ⊔ f iterationIndex ⊔ g approximationDepth

end CompleteLattice

section Entails

open Std.Tactic.BVDecide.LRAT.Internal

variable
  {α σ : Type}
  [Entails α σ]
  (assignment satisfyingAssignment : α → Bool)
  (formula simplifiedFormula : σ)

/-! ## `_ ⊭ _` -/

example : Prop := assignment ⊭ formula

example : Prop := ∀ a : α → Bool, a ⊭ formula

example : Prop :=
  (fun variableIndex => assignment variableIndex && satisfyingAssignment variableIndex) ⊭ formula

example : Prop :=
  (fun variableIndex => assignment variableIndex && !satisfyingAssignment variableIndex) ⊭
    simplifiedFormula

end Entails
