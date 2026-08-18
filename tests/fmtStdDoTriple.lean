import Std.Do
import Std.WP

/-!
Tests for the formatters of the Hoare triple notations: `⦃P⦄ x ⦃Q⦄` of `Std.Do` (`fmtTriple`), as
well as `⦃ P ⦄ x ⦃ Q ⦄`, `⦃ P ⦄ x ⦃ r, Q ⦄`, `⦃ P ⦄ x ⦃ Q; E ⦄` and `⦃ P ⦄ x ⦃ r, Q; E ⦄` of
`Std.WP` (`fmtTripleNotation`, `fmtTripleBinderNotation`, `fmtTripleEPost`,
`fmtTripleBinderEPost`), each of the latter with and without the monad ascription `(m := …)`.

Every section contains forms that fit on one line, forms that exceed the 100 column soft width,
and forms with and without each optional component.
-/

section Triple

open Std.Do

abbrev Counter := StateM Nat

def increment : Counter Nat := do
  let n ← get
  set (n + 1)
  return n

def incrementBy (delta : Nat) : Counter Nat := do
  let n ← get
  set (n + delta)
  return n

def sumArray (xs : Array Nat) : Counter Nat := do
  let mut total := 0
  for x in xs do
    total := total + x
    modify (· + 1)
  return total

variable (xs : Array Nat) (start delta bound : Nat)

/-! ## `⦃_⦄ _ ⦃_⦄` -/

example : Prop := ⦃⌜True⌝⦄ increment ⦃⇓ r s => ⌜r + 1 = s⌝⦄

example : Prop := ⦃fun s => ⌜s = start⌝⦄ incrementBy delta ⦃⇓ r s => ⌜r = start ∧ s = start + delta⌝⦄

example : Prop :=
  ⦃fun s => ⌜s = start ∧ start ≤ bound⌝⦄ incrementBy delta ⦃⇓ r s => ⌜r = start ∧ s = start + delta⌝⦄

example : Prop :=
  ⦃fun s => ⌜s = start ∧ start + delta ≤ bound⌝⦄
  incrementBy delta
  ⦃⇓ r s => ⌜r = start ∧ s = start + delta ∧ s ≤ bound ∧ ∀ k, k ≤ r → k ≤ s⌝⦄

example : Prop := ⦃⌜True⌝⦄ sumArray xs ⦃⇓ r s => ⌜r = xs.sum ∧ s = xs.size⌝⦄

example : Prop :=
  ⦃fun s => ⌜s = 0 ∧ ∀ i, (h : i < xs.size) → xs[i] ≤ bound⌝⦄
  sumArray xs
  ⦃⇓ r s => ⌜r ≤ bound * xs.size ∧ s = xs.size⌝⦄

example : Prop :=
  ⦃⌜True⌝⦄
  (do
    let first ← increment
    let second ← increment
    return first + second)
  ⦃⇓ r s => ⌜r + 3 = 2 * s⌝⦄

example : Prop :=
  ⦃fun s => ⌜s = start⌝⦄
  (do
    let mut seen := 0
    for x in xs do
      if x ≤ bound then
        seen := seen + 1
      else
        seen := seen + (← increment)
    return seen)
  ⦃⇓ r s => ⌜r ≤ xs.size ∧ start ≤ s⌝⦄

end Triple

section InternalTriple

open Std.WP
open Lean.Order

abbrev Fallible := ExceptT String (StateM Nat)

def fib (n : Nat) : Id Nat := do
  let mut a := 0
  let mut b := 1
  for _ in List.range n do
    (a, b) := (b, a + b)
  return a

def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)

def spend (budget : Nat) : Fallible Nat := do
  let remaining ← get
  if remaining < budget then
    throw s!"budget of {remaining} is too small"
  set (remaining - budget)
  return remaining

variable {m : Type → Type} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
variable (xs : Array Nat) (n budget limit : Nat)

/-! ## `⦃ _ ⦄ _ ⦃ _ ⦄` -/

example : Prop := ⦃ True ⦄ fib n ⦃ fun r => r = fibSpec n ⦄

example : Prop := ⦃ 0 < n ∧ n ≤ limit ⦄ fib n ⦃ fun r => r = fibSpec n ∧ r ≤ fibSpec limit ⦄

example : Prop :=
  ⦃ 0 < n ∧ n ≤ limit ∧ fibSpec limit ≤ budget ⦄
  fib n
  ⦃ fun r => r = fibSpec n ∧ r ≤ fibSpec limit ∧ r ≤ budget ∧ ∀ k ≤ n, fibSpec k ≤ r ⦄

example : Prop := ⦃ ⊤ ⦄ (m := m) (pure 4 : m Nat) ⦃ fun r => ⌜r = 4⌝ ⦄

example : Prop :=
  ⦃ ⊤ ⦄
  (m := m)
  (do
    let mut sum := 0
    for x in xs do
      sum := sum + x
    return sum)
  ⦃ fun r => ⌜r = xs.sum⌝ ⦄

/-! ## `⦃ _ ⦄ _ ⦃ _, _ ⦄` -/

example : Prop := ⦃ True ⦄ fib n ⦃ r, r = fibSpec n ⦄

example : Prop := ⦃ 0 < n ∧ n ≤ limit ⦄ fib n ⦃ result, result = fibSpec n ∧ result ≤ fibSpec limit ⦄

example : Prop :=
  ⦃ 0 < n ∧ n ≤ limit ∧ fibSpec limit ≤ budget ⦄
  fib n
  ⦃ result, result = fibSpec n ∧ result ≤ fibSpec limit ∧ result ≤ budget ∧ 0 < result ⦄

example : Prop := ⦃ ⊤ ⦄ (m := m) (pure 4 : m Nat) ⦃ r, ⌜r = 4⌝ ⦄

example : Prop :=
  ⦃ ⊤ ⦄
  (m := m)
  (do
    let mut sum := 0
    for x in xs do
      sum := sum + x
    return sum)
  ⦃ sum, ⌜sum = xs.sum⌝ ⦄

/-! ## `⦃ _ ⦄ _ ⦃ _; _ ⦄` -/

example : Prop := ⦃ fun s => budget ≤ s ⦄ spend budget ⦃ fun _ s => s = 0; epost⟨fun _ _ => False⟩ ⦄

example : Prop :=
  ⦃ fun s => s = limit ⦄
  spend budget
  ⦃ fun r s => r = limit ∧ s = limit - budget; epost⟨fun _ s => s = limit ∧ s < budget⟩ ⦄

example : Prop :=
  ⦃ fun s => s = limit ∧ budget ≤ limit ⦄
  spend budget
  ⦃ fun r s => r = limit ∧ s = limit - budget ∧ s ≤ limit;
    epost⟨fun message s => message ≠ "" ∧ s = limit ∧ s < budget⟩ ⦄

/-! ## `⦃ _ ⦄ _ ⦃ _, _; _ ⦄` -/

example : Prop := ⦃ fun s => budget ≤ s ⦄ spend budget ⦃ r, fun s => s = r; epost⟨fun _ _ => False⟩ ⦄

example : Prop :=
  ⦃ fun s => s = limit ⦄
  spend budget
  ⦃ remaining, fun s => remaining = limit ∧ s = limit - budget; epost⟨fun _ s => s = limit⟩ ⦄

example : Prop :=
  ⦃ fun s => s = limit ∧ budget ≤ limit ⦄
  spend budget
  ⦃ remaining, fun s => remaining = limit ∧ s = limit - budget ∧ s ≤ limit;
    epost⟨fun message s => message ≠ "" ∧ s = limit ∧ s < budget⟩ ⦄

end InternalTriple
