/-
Tests for Lean.Data.IntervalTree
-/
import Lean.Data.IntervalTree

open Lean

-- Sort a list of pairs for deterministic comparison in tests.
private def sortPairs (l : List (Int × Int)) : List (Int × Int) :=
  l.mergeSort (fun (a₁, b₁) (a₂, b₂) => a₁ < a₂ || (a₁ == a₂ && b₁ < b₂))

private def sortTriples (l : List (Int × Int × String)) : List (Int × Int × String) :=
  l.mergeSort (fun (a₁, b₁, _) (a₂, b₂, _) => a₁ < a₂ || (a₁ == a₂ && b₁ < b₂))

-- Abbreviations for brevity.
private abbrev ISet := IntervalSet Int compare
private abbrev IMap := IntervalMap Int String compare

-- ---------------------------------------------------------------------------
-- Basic operations
-- ---------------------------------------------------------------------------

-- Inserting into an empty set gives a singleton.
#guard
  let s : ISet := (∅ : ISet).insert 1 5
  s.contains 1 5 && !s.contains 2 5

-- Inserting the same interval twice is idempotent (for a set).
#guard
  let s : ISet := (∅ : ISet).insert 1 5 |>.insert 1 5
  s.size == 1

-- Erasing a present interval removes it.
#guard
  let s : ISet := (∅ : ISet).insert 1 5 |>.insert 2 8
  let s' := s.erase 1 5
  !s'.contains 1 5 && s'.contains 2 8

-- Erasing an absent interval is a no-op.
#guard
  let s : ISet := (∅ : ISet).insert 1 5
  (s.erase 2 8).size == s.size

-- isEmpty works correctly.
#guard
  let s : ISet := ∅
  s.isEmpty && !(s.insert 1 5 |>.isEmpty)

-- find? returns the right value and none for missing keys.
#guard
  let m : IMap := (∅ : IMap).insert 1 5 "hello" |>.insert 3 7 "world"
  m.find? 1 5 == some "hello" && m.find? 3 7 == some "world" && m.find? 2 6 == none

-- insert updates an existing interval's value.
#guard
  let m : IMap := (∅ : IMap).insert 1 5 "old" |>.insert 1 5 "new"
  m.find? 1 5 == some "new" && m.size == 1

-- ---------------------------------------------------------------------------
-- toList / ofList round-trip
-- ---------------------------------------------------------------------------

-- toList returns entries in ascending (lo, hi) order.
#guard
  let s : ISet := (∅ : ISet).insert 3 7 |>.insert 1 5 |>.insert 1 3 |>.insert 5 9
  s.toList == [(1, 3), (1, 5), (3, 7), (5, 9)]

-- ofList round-trips with toList.
#guard
  let triples : List (Int × Int × String) :=
    [(1, 5, "A"), (3, 7, "B"), (0, 10, "C")]
  let m : IMap := IntervalMap.ofList triples
  m.size == 3 && m.find? 3 7 == some "B"

-- ---------------------------------------------------------------------------
-- findAllOverlapping
-- ---------------------------------------------------------------------------

-- Build a representative set for overlap tests:
--   [1, 3], [2, 6], [5, 8], [7, 10], [0, 10]
private def overlapSet : ISet :=
  (∅ : ISet).insert 1 3 |>.insert 2 6 |>.insert 5 8 |>.insert 7 10 |>.insert 0 10

-- [4, 5] overlaps [2,6], [5,8], [0,10].
#guard sortPairs (overlapSet.findAllOverlapping 4 5) == [(0, 10), (2, 6), (5, 8)]

-- [1, 1] overlaps [1,3], [0,10].
#guard sortPairs (overlapSet.findAllOverlapping 1 1) == [(0, 10), (1, 3)]

-- [6, 7] overlaps [2,6], [5,8], [7,10], [0,10].
#guard sortPairs (overlapSet.findAllOverlapping 6 7) == [(0, 10), (2, 6), (5, 8), (7, 10)]

-- [11, 12] overlaps nothing.
#guard overlapSet.findAllOverlapping 11 12 == []

-- [-1, 0] overlaps [0,10].
#guard sortPairs (overlapSet.findAllOverlapping (-1) 0) == [(0, 10)]

-- A single-point query [3,3].
#guard sortPairs (overlapSet.findAllOverlapping 3 3) == [(0, 10), (1, 3), (2, 6)]

-- ---------------------------------------------------------------------------
-- findAllContaining
-- ---------------------------------------------------------------------------

-- Set: [0,10], [1,8], [2,6], [3,5], [4,4]
private def containingSet : ISet :=
  (∅ : ISet).insert 0 10 |>.insert 1 8 |>.insert 2 6 |>.insert 3 5 |>.insert 4 4

-- [3,5] is contained in [0,10], [1,8], [2,6], [3,5].
#guard sortPairs (containingSet.findAllContaining 3 5) == [(0, 10), (1, 8), (2, 6), (3, 5)]

-- [4,4] is contained in everything.
#guard
  sortPairs (containingSet.findAllContaining 4 4) ==
    [(0, 10), (1, 8), (2, 6), (3, 5), (4, 4)]

-- [0,10] is only contained in itself.
#guard sortPairs (containingSet.findAllContaining 0 10) == [(0, 10)]

-- [2,9] is only contained in [0,10]: [1,8] requires 8≥9, which fails.
#guard sortPairs (containingSet.findAllContaining 2 9) == [(0, 10)]

-- [-1, 11] is not contained by anyone.
#guard containingSet.findAllContaining (-1) 11 == []

-- ---------------------------------------------------------------------------
-- findSmallestContaining
-- ---------------------------------------------------------------------------

-- For query [3,5], the smallest containing interval is [3,5] itself.
#guard sortPairs (containingSet.findSmallestContaining 3 5) == [(3, 5)]

-- For query [4,4], the smallest containing is [4,4] itself.
#guard sortPairs (containingSet.findSmallestContaining 4 4) == [(4, 4)]

-- For query [0,10], the only containing interval is [0,10].
#guard sortPairs (containingSet.findSmallestContaining 0 10) == [(0, 10)]

-- When the exact interval is absent, we get the tightest wrapper(s).
-- Set: [0,10], [1,9]. Query [2,8] → smallest is [1,9].
#guard
  let s : ISet := (∅ : ISet).insert 0 10 |>.insert 1 9
  sortPairs (s.findSmallestContaining 2 8) == [(1, 9)]

-- Multiple non-comparable minimal containers.
-- [1,6] and [3,9] both contain [3,6] but neither contains the other → both returned.
#guard
  let s : ISet := (∅ : ISet).insert 0 10 |>.insert 1 6 |>.insert 3 9
  sortPairs (s.findSmallestContaining 3 6) == [(1, 6), (3, 9)]

-- ---------------------------------------------------------------------------
-- findAllContainedIn
-- ---------------------------------------------------------------------------

-- Set: [1,3], [2,5], [4,6], [0,10], [3,3]
private def containedSet : ISet :=
  (∅ : ISet).insert 1 3 |>.insert 2 5 |>.insert 4 6 |>.insert 0 10 |>.insert 3 3

-- [1,6] contains [1,3], [2,5], [3,3], [4,6] (4≤6 and 6≤6 ✓).
#guard sortPairs (containedSet.findAllContainedIn 1 6) == [(1, 3), (2, 5), (3, 3), (4, 6)]

-- [0,10] contains everything.
#guard
  sortPairs (containedSet.findAllContainedIn 0 10) ==
    [(0, 10), (1, 3), (2, 5), (3, 3), (4, 6)]

-- [3,3] contains only [3,3].
#guard sortPairs (containedSet.findAllContainedIn 3 3) == [(3, 3)]

-- [2,4]: [3,3] satisfies 2≤3 and 3≤4. Others fail.
#guard sortPairs (containedSet.findAllContainedIn 2 4) == [(3, 3)]

-- Nothing is contained in an "empty" (inverted) range.
#guard containedSet.findAllContainedIn 5 3 == []

-- ---------------------------------------------------------------------------
-- IntervalMap (with values)
-- ---------------------------------------------------------------------------

private def sampleMap : IMap :=
  (∅ : IMap)
    |>.insert 0 10 "wide"
    |>.insert 1 8  "mid"
    |>.insert 3 5  "narrow"

-- findAllContaining returns correct values.
#guard
  sortTriples (sampleMap.findAllContaining 3 5) ==
    [(0, 10, "wide"), (1, 8, "mid"), (3, 5, "narrow")]

-- findSmallestContaining returns the narrowest interval and its value.
#guard sortTriples (sampleMap.findSmallestContaining 3 5) == [(3, 5, "narrow")]

-- findAllContainedIn: everything in map is inside [0,10].
#guard
  sortTriples (sampleMap.findAllContainedIn 0 10) ==
    [(0, 10, "wide"), (1, 8, "mid"), (3, 5, "narrow")]

-- ---------------------------------------------------------------------------
-- ForIn iteration
-- ---------------------------------------------------------------------------

-- for loop visits all entries in ascending order.
#guard
  let s : ISet := (∅ : ISet).insert 3 7 |>.insert 1 5 |>.insert 1 3
  let entries := Id.run do
    let mut acc : List (Int × Int) := []
    for (lo, hi, _) in s do
      acc := acc ++ [(lo, hi)]
    pure acc
  entries == [(1, 3), (1, 5), (3, 7)]

-- ---------------------------------------------------------------------------
-- Edge cases
-- ---------------------------------------------------------------------------

-- Empty tree queries return empty results.
#guard
  let s : ISet := ∅
  s.findAllOverlapping 0 10 == [] &&
  s.findAllContaining 0 10 == [] &&
  s.findAllContainedIn 0 10 == [] &&
  s.findSmallestContaining 0 10 == []

-- Point intervals [n, n] work correctly.
#guard
  let s : ISet := (∅ : ISet).insert 1 1 |>.insert 2 2 |>.insert 3 3
  sortPairs (s.findAllOverlapping 2 2) == [(2, 2)] &&
  sortPairs (s.findAllContaining 2 2) == [(2, 2)] &&
  sortPairs (s.findAllContainedIn 1 3) == [(1, 1), (2, 2), (3, 3)]

-- Intervals sharing an endpoint are both found in overlap queries.
#guard
  let s : ISet := (∅ : ISet).insert 1 5 |>.insert 5 9
  sortPairs (s.findAllOverlapping 5 5) == [(1, 5), (5, 9)]

-- Identical interval inserted twice is stored only once (set semantics).
#guard
  let s : ISet := (∅ : ISet).insert 0 10 |>.insert 0 10 |>.insert 1 9 |>.insert 2 8
  s.size == 3

-- Large sequential insertion preserves correctness.
-- Intervals [i, i+5] for i in 0..19.  Query [7,8]:
-- overlapping intervals are [lo, lo+5] where lo ≤ 8 and lo+5 ≥ 7, i.e., lo ∈ [2,8].
-- That's indices 2,3,4,5,6,7,8 → 7 intervals? Wait: lo ∈ {2,3,4,5,6,7,8} → 7 intervals.
-- Let's compute: lo ≤ 8 (gives lo ≤ 8) and lo+5 ≥ 7 (gives lo ≥ 2). So lo ∈ {2..8} → 7.
#guard
  let s : ISet := (List.range 20).foldl (fun s i =>
    s.insert (Int.ofNat i) (Int.ofNat i + 5)) (∅ : ISet)
  s.size == 20 &&
  (sortPairs (s.findAllOverlapping 7 8)).length == 7
