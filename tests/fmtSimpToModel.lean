import Std.Data.DHashMap.Internal.RawLemmas
import Std.Data.DTreeMap.Internal.Lemmas

/-!
Tests for the `simp_to_model` formatters (`fmtHashMapSimpToModel`, `fmtTreeMapSimpToModel`):
the bare tactic, the optional `[...]` list of query names in various lengths, the optional
`using` term, and combinations of the two that force breaks in different places.
-/

section HashMap

open Std.DHashMap.Internal Std.DHashMap.Internal.Raw₀

example : True := by
  simp_to_model

example : True := by
  simp_to_model [toList, toArray]

example : True := by
  simp_to_model [insert, contains]

example : True := by
  simp_to_model using List.isEmpty_insertEntry

example : True := by
  simp_to_model [insert, isEmpty] using List.isEmpty_insertEntry

example : True := by
  simp_to_model [isEmpty, contains] using List.isEmpty_eq_false_iff_exists_containsKey

example : True := by
  simp_to_model [erase, isEmpty, contains] using List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false

example : True := by
  simp_to_model [diff, contains, get!] using
    List.getValueCastD_filter_not_contains_map_fst_of_containsKey_eq_false_right

example : True := by
  simp_to_model [insert, insertIfNew, erase, isEmpty, size, contains, get?, get, get!, getD, toList,
    toArray, keys, keysArray]

example : True := by
  simp_to_model [insert, insertIfNew, erase, isEmpty, size, contains, get?, get, get!, getD] using
    List.containsKey_insertEntryIfNew

example : True := by
  simp_to_model [Const.toList, Const.toArray, keys, keysArray, foldM, fold, foldRevM, foldRev,
    forIn, forM, toArray] using List.getValue?_eq_some_iff

example : True := by
  simp_to_model [insert, get?] using
    (List.getValueCast?_insertEntry (k := k) (v := v) (l := toListModel m.1.buckets)).symm

end HashMap

section TreeMap

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

example : True := by
  simp_to_model

example : True := by
  simp_to_model [filter, map, filterMap]

example : True := by
  simp_to_model [contains] using List.containsKey_congr

example : True := by
  simp_to_model [erase, isEmpty, contains] using List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false

example : True := by
  simp_to_model [keyAtIdx!, keyAtIdxD, Equiv, filter, map, filterMap] using
    List.getValueD_filter_not_contains_map_fst_of_containsKey_eq_false_left

end TreeMap
