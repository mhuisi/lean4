/-!
Tests for the quantifier formatter (`fmtQuantifier`): single quantifiers, chains of nested
quantifiers of the same kind, and chains that span several quantifier kinds (`∀`, `∃`, `exists`,
`Σ`, `Σ'`, and the binder predicate variants `∀ x > 0,` / `∃ x > 0,`).
-/

variable
  (p q : Nat → Prop)
  (r : Nat → Nat → Prop)
  (s : Nat → Nat → Nat → Prop)
  (f g : Nat → Nat)
  (dist : Nat → Nat → Nat)
  (IsContinuousAtEveryPointOfTheDomain : (Nat → Nat) → Prop)

/-! ## Single quantifiers -/

example : Prop := ∀ x, p x

example : Prop := ∃ x, p x

example : Prop := ∀ x y z : Nat, s x y z

example : Prop := ∃ x y, r x y

example : Prop := exists x, p x

example : Type := Σ x, Fin x

example : Type := Σ' x, Fin x

example : Prop := ∀ {α : Type} [inst : Inhabited α] (xs : List α), xs.head? = xs.get? 0

example : Prop := ∀ ε > 0, p ε

example : Prop := ∃ δ > 0, q δ

/-! ## Chains of quantifiers of the same kind -/

example : Prop := ∀ x, ∀ y, r x y

example : Prop := ∃ x, ∃ y, r x y

example : Prop :=
  ∀ numberOfElements, ∀ numberOfBuckets, ∀ numberOfCollisions,
    s numberOfElements numberOfBuckets numberOfCollisions

/-! ## Chains that span several quantifier kinds -/

example : Prop := ∀ x, ∃ y, r x y

example : Prop := ∃ x, ∀ y, r x y

example : Prop := ∀ x, ∃ y, ∀ z, s x y z

example : Prop := ∀ ε > 0, ∃ δ > 0, ∀ x, dist (f x) (g x) < ε

example : Prop := ∃ bound, ∀ index ≥ bound, ∀ offset, p (index + offset)

example : Type := Σ dimension, Σ' basis : Fin dimension → Nat, Fin (basis 0)

example : Prop := ∀ x, exists y, r x y

/-! ## Chains that have to break -/

example : Prop :=
  ∀ inputSequence, ∃ outputSequence, ∀ index, r (inputSequence index) (outputSequence index)

example : Prop :=
  ∀ (approximationError : Nat) (_ : approximationError > 0),
    ∃ (sampleSize : Nat) (_ : sampleSize > 0),
      ∀ observedFrequency, dist observedFrequency sampleSize < approximationError

example : Prop :=
  ∀ toleratedError > 0, ∃ requiredPrecision > 0, ∀ candidateSolution, ∀ referenceSolution,
    dist (f candidateSolution) (g referenceSolution) < toleratedError

example : Prop :=
  ∃ leastUpperBound,
    ∀ candidate,
      (∀ element, r element candidate) → dist leastUpperBound candidate = 0

/-! ## Quantifiers with bodies that break on their own -/

example : Prop :=
  ∀ x, ∃ y,
    if r x y then
      p (f x)
    else
      q (g y)

example : Prop :=
  ∀ transformation, ∀ input,
    IsContinuousAtEveryPointOfTheDomain transformation ∧
      IsContinuousAtEveryPointOfTheDomain fun result => transformation (input + result)

example : Prop :=
  ∀ x, ∃ y, r x y ∧ r y x ∧ p x ∧ q y ∧ p y ∧ q x ∧ r (f x) (g y) ∧ r (g y) (f x) ∧ p (f (g x))

/-! ## Quantifiers as arguments and in nested positions -/

example : Prop := p 0 ∧ ∀ x, ∃ y, r x y

example : Prop := (∀ x, ∃ y, r x y) → ∃ z, ∀ w, r z w

example : Prop :=
  ∀ x, (∃ y, r x y) ∨ ∀ z, ¬r x z
