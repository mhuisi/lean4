import Lean

/-!
Tests for the `try?`-family formatters (`fmtTryTrace`, `fmtTryTraceWith`, `fmtAttemptAll`,
`fmtAttemptAllPar`, `fmtFirstPar`, `fmtTryResult` and `fmtRegisterTryTactic`): the `try?` tactic
with and without a trailing `=> ...` tactic sequence, the `attempt_all`, `attempt_all_par` and
`first_par` helper tactics, the `try_suggestions` helper tactic and the `register_try?_tactic`
command. The examples vary the number of configuration items, the number and size of the
alternatives, and the presence of doc comments and priorities so that the layouts have to break in
different places.
-/

namespace TryFormatterTests

/-! `try?` -/

example (a b : Nat) : a + b = b + a := by try?

example (a b : Nat) : a + b = b + a := by try? +missing

example (xs : List Nat) : xs.reverse.reverse = xs := by try? (max := 4) -only

example (n : Nat) : n ≤ n + 1 := by try? (max := 16) +harder +missing -only -main -name

example (n : Nat) : n ≤ n + 1 := by try? (max := 16) +harder +missing +merge -only -main -name +targetOnly

example (xs ys : List Nat) : (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  try? (config := { max := 12, harder := true, merge := false }) +missing -only +targetOnly

/-! `try? => ...` -/

example (a b : Nat) : a + b = b + a := by try? => simp

example (a b : Nat) : a + b = b + a := by try? +missing => simp [Nat.add_comm]

example (xs : List Nat) : xs.length = xs.reverse.length := by
  try? (max := 2) => simp only [List.length_reverse]

example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  try? (max := 3) +harder =>
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.succ_add]

example (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  try? (max := 8) +harder +missing -only -main -name +targetOnly => omega

/-! `attempt_all` -/

example (a : Nat) : a = a := by
  attempt_all
    | rfl
    | simp

example (xs : List Nat) : xs ++ [] = xs := by
  attempt_all
    | simp
    | grind only [List.append_nil]
    | induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih]

/-! `attempt_all_par` -/

example (a : Nat) : a = a := by
  attempt_all_par
    | rfl
    | simp

example (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by
  attempt_all_par
    | omega
    | simp only [Nat.le_succ_of_le, h]
    | exact Nat.le_succ_of_le h

/-! `first_par` -/

example (a : Nat) : a = a := by
  first_par
    | rfl
    | simp

example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  first_par
    | simp
    | grind only [List.length_append]
    | induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, Nat.succ_add]

/-! `try_suggestions` -/

example (a : Nat) : a = a := by try_suggestions rfl

example (a : Nat) : a = a := by try_suggestions rfl trivial simp

example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  try_suggestions (simp only [List.length_append]) (grind only [List.length_append]) omega

example (n m : Nat) (h : n ≤ m) : n ≤ m + 1 := by
  try_suggestions (omega) (simp only [Nat.le_succ_of_le, h]) (exact Nat.le_succ_of_le h) (grind only [Nat.le_succ_of_le])

/-! `register_try?_tactic` -/

register_try?_tactic omega

register_try?_tactic (priority := 500) simp_arith

/--
Registers `bv_decide` as a suggestion generator for `try?`, at a low priority because it is
comparatively expensive to run.
-/
register_try?_tactic (priority := 100) bv_decide

register_try?_tactic (priority := 250) simp +arith only [Nat.add_comm, Nat.mul_comm, Nat.add_assoc, Nat.mul_assoc]

register_try?_tactic (priority := 750)
  first
    | omega
    | simp_arith
    | grind only

/-- Registers a decision procedure that first normalizes the goal. -/
register_try?_tactic
  simp only [Nat.add_comm, Nat.mul_comm] <;> omega

end TryFormatterTests
