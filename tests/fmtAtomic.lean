/-!
Tests the formatter derived for syntax that consists exclusively of atoms
(`derivedAtomicFmtProvider`). None of the syntax below has a formatter of its own, so the
`missingFormatter` linter enabled here must stay silent for all of it.
-/

set_option linter.missingFormatter true

example : True := by
  first
    | skip
    | done
  trivial

example (h : False) : True := by
  exfalso
  contradiction

example (a : Nat) : a = a := by
  first
    | rfl
    | eq_refl
    | ac_rfl
    | apply_rfl
    | rfl'

example (p : Prop) (h : p) : p := by
  first
    | assumption
    | trivial

example : True ∧ True := by
  and_intros
  · trivial
  · trivial

example (p : Prop) : p ∨ True := by
  right
  trivial

example (p : Prop) : True ∨ p := by
  left
  trivial

example (a b : Nat) (h : a = b) : b = a := by
  subst_vars
  rfl

example : Nonempty Nat := by
  constructor
  expose_names
  exact 0

example (a : Nat) : a = a := by
  false_or_by_contra
  simp at *

example : Inhabited Nat := by infer_instance

example : ¬ (0 = 1) := by nofun

example (a : Nat) : a + 0 = a := by
  conv =>
    lhs
    whnf
    rfl

example (a b : Nat) : a + b = a + b := by
  conv =>
    lhs
    congr
    · skip
    · skip

example (f : Nat → Nat) (h : ∀ x, f x = x) : f 0 = 0 := by
  conv =>
    rhs
    skip
  conv =>
    lhs
    rw [h]

example (a : Nat × Nat) : a.1 = a.1 := by
  obtain ⟨-, -⟩ := a
  rfl

example (p q : Prop) : p → q → True := by
  rintro _ -
  trivial

example (a : Nat) (h : a = 0) : a = 0 := by
  simp only [h] at *

@[simp ↓] theorem simpPreTest : (0 : Nat) + 0 = 0 := by simp

@[simp ↑] theorem simpPostTest : (0 : Nat) * 1 = 0 := by simp

opaque IsFoo : Nat → Prop

@[grind →] theorem grindFwdTest (n : Nat) (h : IsFoo n) : IsFoo n ∨ IsFoo n := Or.inl h

@[grind cases] inductive GrindCasesTest : Nat → Prop where
  | mk : GrindCasesTest 0

@[grind intro] inductive GrindIntroTest : Nat → Prop where
  | mk : GrindIntroTest 0

example : (∅ : List Nat) = [] := rfl

notation:max "myAtom" => (0 : Nat)

example : myAtom = 0 := rfl

/-- info: 1 -/
#guard_msgs (whitespace := lax) in #eval 1

/-- info: 1 -/
#guard_msgs (info) in #eval 1

/-- info: 1 -/
#guard_msgs (check info, drop warning) in #eval 1

/-- info: 1 -/
#guard_msgs (ordering := exact) in #eval 1

/-- info: 1 -/
#guard_msgs (positions := false) in #eval 1

def wfTest : Nat → Nat
  | 0 => 0
  | n + 1 => wfTest n
termination_by n => n
decreasing_by decreasing_tactic
