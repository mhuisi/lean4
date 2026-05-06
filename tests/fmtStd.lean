import Std.Data.DHashMap.RawLemmas
import Std.Sat.AIG
import Std.Tactic.BVDecide
import Std.Time

/-!
Tests for the formatters of `Std`-specific syntax: `simp_to_raw` (`fmtSimpToRaw`), the
`bv_decide` family of tactics and attributes (`fmtBvCheck`, `fmtStdBvDecide`, `fmtStdBvTrace`,
`fmtStdBvNormalize`, `fmtBvNormalizeAttr`, `fmtBvNormalizeProcBuiltinAttr`), the AIG denotation
notations `⟦_, _⟧` and `⟦_, _, _⟧` (`fmtAIGDenote`, `fmtAIGDenoteEntrypoint`), and
`datespec(...)` (`fmtDatespec`, `fmtDatespecWithConfig`). Every section contains forms that fit
on one line, forms that exceed the 100 column soft width, and forms with and without each
optional component.
-/

section SimpToRaw

open Std.DHashMap.Internal.Raw

example : True := by
  simp_to_raw

example : True := by
  simp_to_raw using List.containsKey_insertEntry

example : True := by
  simp_to_raw using List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false

example : True := by
  simp_to_raw using List.getValueCastD_filter_not_contains_map_fst_of_containsKey_eq_false_right

example : True := by
  simp_to_raw using
    (List.getValueCast?_insertEntry (k := k) (v := v) (l := toListModel m.1.buckets)).symm

example : True := by
  simp_to_raw using
    List.getValue?_insertManyIfNewUnit_list_of_containsKey_eq_false_of_mem_of_distinct_keys

end SimpToRaw

section BVDecide

example (x y : BitVec 8) : x + y = y + x := by
  bv_decide

example (x y : BitVec 8) : x &&& y = y &&& x := by
  bv_decide (timeout := 1)

example (x y : BitVec 8) : x ||| y = y ||| x := by
  bv_decide +acNf -structures (timeout := 1)

example (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  bv_decide +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 1)

example (x y : BitVec 8) : x + y = y + x := by
  bv_decide?

example (x y z : BitVec 8) : x + (y + z) = (y + z) + x := by
  bv_decide? +acNf -embeddedConstraintSubst (timeout := 1)

example (x y : BitVec 8) : x + y = y + x := by
  bv_check "bv_add_comm.lrat"

example (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  bv_check +acNf -structures (timeout := 1) "bv_xor_comm.lrat"

example (x y : BitVec 16) : x * y = y * x := by
  bv_check +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 1)
    "bv_mul_comm.lrat"

example (x y : BitVec 8) : x + y = y + x := by
  bv_normalize

example (x y : BitVec 8) : x + y = y + x := by
  bv_normalize +acNf

example (x y : BitVec 8) : x &&& y = y &&& x := by
  bv_normalize (maxSteps := 10000)

example (x y : BitVec 8) : x ||| y = y ||| x := by
  bv_normalize +acNf -structures (timeout := 60)

example (x y : BitVec 16) : x ^^^ y = y ^^^ x := by
  bv_normalize +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 120)

example (x y : BitVec 16) : x * y = y * x := by
  bv_normalize +acNf +shortCircuit +graphviz -structures -fixedInt -enums -andFlattening
    -embeddedConstraintSubst (maxSteps := 100000) (timeout := 120) (solverMode := .counterexample)

@[bv_normalize]
theorem BitVec.and_self_left' (x y : BitVec w) : x &&& (x &&& y) = x &&& y := sorry

@[bv_normalize ↓]
theorem BitVec.or_self_left' (x y : BitVec w) : x ||| (x ||| y) = x ||| y := sorry

@[bv_normalize ←]
theorem BitVec.xor_assoc' (x y z : BitVec w) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := sorry

@[bv_normalize ↑ 500]
theorem BitVec.add_zero' (x : BitVec w) : x + 0#w = x := sorry

@[bv_normalize ↓ ← 10000]
theorem BitVec.mul_one_of_shift_left_and_add_carry_bits (x : BitVec w) : x * 1#w = x := sorry

attribute [bv_normalize ↓ ← 100] BitVec.and_self_left'

attribute [builtin_bv_normalize_proc] BitVec.or_self_left'

attribute [builtin_bv_normalize_proc ↑] BitVec.xor_assoc'

end BVDecide

section AIG

open Std.Sat Std.Sat.AIG

variable {α : Type} [Hashable α] [DecidableEq α] {aig : AIG α} {assign : α → Bool}
    {gate : Nat} {inv : Bool}

example (entry : Entrypoint α) : ⟦entry, assign⟧ = ⟦entry.aig, entry.ref, assign⟧ := sorry

example (hgate : gate < aig.decls.size) :
    ⟦aig, ⟨gate, !inv, hgate⟩, assign⟧ = !⟦aig, ⟨gate, inv, hgate⟩, assign⟧ := sorry

example (input : BinaryInput aig) :
    ⟦aig.mkGate input, assign⟧ = (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧) := sorry

example (entry : Entrypoint α) (input : BinaryInput entry.aig) :
    ⟦(entry.aig.mkGateCached input).aig, entry.ref.cast (by simp), assign⟧ = ⟦entry, assign⟧ :=
  sorry

example (entry : Entrypoint α) (input : BinaryInput entry.aig) :
    ⟦(entry.aig.mkGateCached input).aig, ⟨entry.ref.gate, entry.ref.invert, by apply LawfulOperator.lt_size_of_lt_aig_size; omega⟩, assign⟧ =
      ⟦entry, assign⟧ :=
  sorry

example (s : RefVecEntry α n) (idx : Nat) (hidx : idx < n) (input : BinaryInput s.aig) :
    ⟦(s.aig.mkGateCached input).aig, (s.vec.get idx hidx).cast (by simp [LawfulOperator.le_size]), assign⟧ =
      ⟦s.aig, s.vec.get idx hidx, assign⟧ :=
  sorry

end AIG

section DateSpec

open Std.Time

def isoDate : GenericFormat .any := datespec("uuuu-MM-dd")

def isoTimeWithNanos : GenericFormat .any := datespec("HH:mm:ss.SSSSSSSSS")

def isoDateTimeWithZone : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZZZZZ")

def longWeekdayDateTime : GenericFormat (.only .GMT) :=
  datespec("EEEE, MMMM d, uuuu 'at' HH:mm:ss.SSSSSSSSS")

def leapSecondAware : GenericFormat .any :=
  datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZ", { allowLeapSeconds := true })

def strictDateTimeWithZoneName : GenericFormat .any :=
  datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSS'['zzzz']'", { allowLeapSeconds := false })

def verboseDateTimeWithZoneName : GenericFormat .any :=
  datespec("EEEE, MMMM d, uuuu 'at' HH:mm:ss.SSSSSSSSS '['zzzz']' XXX", { allowLeapSeconds := true })

def verboseDateTimeWithConfiguredZoneName : GenericFormat .any :=
  datespec("EEEE, MMMM d, uuuu 'at' HH:mm:ss.SSSSSSSSS '['zzzz']' XXX",
    { allowLeapSeconds := true, dateformat := Std.Time.DateFormat.enUS })

def veryVerboseDateTime : GenericFormat (.only .GMT) :=
  datespec("GGGG EEEE, MMMM d, uuuu 'at' hh:mm:ss.SSSSSSSSS aa '['zzzz']' XXX VV OOOO ZZZZZ")

end DateSpec
