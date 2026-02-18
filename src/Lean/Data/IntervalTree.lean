/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean FRO
-/
module

prelude
public import Lean.Data.RBMap
import Init.WFTactics

public section

namespace Lean

universe u v w

/-!
# Interval Tree

`IntervalMap α β cmp` is a map from closed intervals `[lo, hi]` over an ordered type `α`
(compared by `cmp`) to values of type `β`. Internally it is a red-black BST keyed by `(lo, hi)`
(lexicographic order) with each node augmented by `maxHi`, the maximum right endpoint among all
intervals in that subtree.

The `maxHi` augmentation enables O(log n + k) interval queries (where k is the result count):

- `findAllOverlapping t qlo qhi`   – intervals `[a,b]` with `a ≤ qhi ∧ b ≥ qlo`
- `findAllContaining t qlo qhi`    – intervals `[a,b]` with `a ≤ qlo ∧ b ≥ qhi` (contain `[qlo,qhi]`)
- `findSmallestContaining t qlo qhi` – minimal-under-containment subset of the above
- `findAllContainedIn t qlo qhi`   – intervals `[a,b]` with `a ≥ qlo ∧ b ≤ qhi` (inside `[qlo,qhi]`)

`insert` and `erase` run in O(log n).

For a set of intervals without associated values use `IntervalSet α cmp`, which is an alias for
`IntervalMap α Unit cmp`.
-/

-- ---------------------------------------------------------------------------
-- Internal augmented red-black tree node
-- ---------------------------------------------------------------------------

/-- Raw augmented red-black tree node backing `IntervalMap`.

The BST is ordered lexicographically by `(lo, hi)`.  Every non-leaf node is augmented with
`maxHi`, the maximum `hi` value among all intervals in the subtree.  This enables efficient
pruning during interval queries. -/
inductive IntervalNode (α : Type u) (β : Type v) : Type (max u v) where
  | leaf
  | node (color  : RBColor)
         (left   : IntervalNode α β)
         (lo hi  : α) (val : β) (maxHi : α)
         (right  : IntervalNode α β)

namespace IntervalNode

variable {α : Type u} {β : Type v} {σ : Type w}

/-- Number of intervals stored in the subtree. -/
@[local simp] def size : IntervalNode α β → Nat
  | leaf              => 0
  | node _ l _ _ _ _ r => l.size + r.size + 1

@[inline] def isRed : IntervalNode α β → Bool
  | node .red .. => true
  | _            => false

@[inline] def isBlack : IntervalNode α β → Bool
  | node .black .. => true
  | _              => false

/-- Return the greater of `a` and `b` according to `cmp`. -/
@[inline] private def maxBy (cmp : α → α → Ordering) (a b : α) : α :=
  if cmp a b == .gt then a else b

/-- Compute `maxHi` for a node from its left child, own `hi`, and right child. -/
@[inline] def computeMaxHi (cmp : α → α → Ordering)
    (l : IntervalNode α β) (hi : α) (r : IntervalNode α β) : α :=
  let m := match l with
    | leaf                => hi
    | node _ _ _ _ _ lm _ => maxBy cmp hi lm
  match r with
  | leaf                => m
  | node _ _ _ _ _ rm _ => maxBy cmp m rm

/-- Build a node, automatically computing `maxHi` from children. -/
@[inline] def mkNode (cmp : α → α → Ordering) (c : RBColor)
    (l : IntervalNode α β) (lo hi : α) (v : β) (r : IntervalNode α β) : IntervalNode α β :=
  node c l lo hi v (computeMaxHi cmp l hi r) r

/-- Lexicographic comparison of interval keys `(lo, hi)`. -/
@[inline] def cmpInterval (cmp : α → α → Ordering) (lo1 hi1 lo2 hi2 : α) : Ordering :=
  match cmp lo1 lo2 with
  | .eq => cmp hi1 hi2
  | o   => o

-- ---------------------------------------------------------------------------
-- Rebalancing  (adapted from RBMap to recompute maxHi after rotations)
-- ---------------------------------------------------------------------------

/-- Fix a red-red violation in the left child. -/
@[inline] def balance1 (cmp : α → α → Ordering) :
    IntervalNode α β → α → α → β → IntervalNode α β → IntervalNode α β
  | node .red (node .red a kxlo kxhi vx _ b) kylo kyhi vy _ c, kzlo, kzhi, vz, d
  | node .red a kxlo kxhi vx _ (node .red b kylo kyhi vy _ c), kzlo, kzhi, vz, d =>
    mkNode cmp .red
      (mkNode cmp .black a kxlo kxhi vx b)
      kylo kyhi vy
      (mkNode cmp .black c kzlo kzhi vz d)
  | l, klo, khi, v, r => mkNode cmp .black l klo khi v r

/-- Fix a red-red violation in the right child. -/
@[inline] def balance2 (cmp : α → α → Ordering) :
    IntervalNode α β → α → α → β → IntervalNode α β → IntervalNode α β
  | a, kxlo, kxhi, vx, node .red (node .red b kylo kyhi vy _ c) kzlo kzhi vz _ d
  | a, kxlo, kxhi, vx, node .red b kylo kyhi vy _ (node .red c kzlo kzhi vz _ d) =>
    mkNode cmp .red
      (mkNode cmp .black a kxlo kxhi vx b)
      kylo kyhi vy
      (mkNode cmp .black c kzlo kzhi vz d)
  | l, klo, khi, v, r => mkNode cmp .black l klo khi v r

-- ---------------------------------------------------------------------------
-- Insertion
-- ---------------------------------------------------------------------------

@[specialize] def ins (cmp : α → α → Ordering) (lo hi : α) (v : β) :
    IntervalNode α β → IntervalNode α β
  | leaf => mkNode cmp .red leaf lo hi v leaf
  | node .red l klo khi kv _ r =>
    match cmpInterval cmp lo hi klo khi with
    | .lt => mkNode cmp .red (ins cmp lo hi v l) klo khi kv r
    | .gt => mkNode cmp .red l klo khi kv (ins cmp lo hi v r)
    | .eq => mkNode cmp .red l lo hi v r
  | node .black l klo khi kv _ r =>
    match cmpInterval cmp lo hi klo khi with
    | .lt => balance1 cmp (ins cmp lo hi v l) klo khi kv r
    | .gt => balance2 cmp l klo khi kv (ins cmp lo hi v r)
    | .eq => mkNode cmp .black l lo hi v r

@[inline] def setBlack : IntervalNode α β → IntervalNode α β
  | node _ l lo hi v m r => node .black l lo hi v m r
  | leaf => leaf

@[specialize] def insert (cmp : α → α → Ordering) (lo hi : α) (v : β)
    (t : IntervalNode α β) : IntervalNode α β :=
  (ins cmp lo hi v t).setBlack

-- ---------------------------------------------------------------------------
-- Deletion  (Kahrs / RBMap approach, adapted for maxHi augmentation)
-- ---------------------------------------------------------------------------

@[inline] def setRed : IntervalNode α β → IntervalNode α β
  | node _ l lo hi v m r => node .red l lo hi v m r
  | leaf => leaf

def balLeft (cmp : α → α → Ordering) :
    IntervalNode α β → α → α → β → IntervalNode α β → IntervalNode α β
  | node .red a kxlo kxhi vx _ b, klo, khi, v, r =>
    mkNode cmp .red (mkNode cmp .black a kxlo kxhi vx b) klo khi v r
  | l, klo, khi, v, node .black a kylo kyhi vy _ b =>
    balance2 cmp l klo khi v (mkNode cmp .red a kylo kyhi vy b)
  | l, klo, khi, v,
    node .red (node .black a kylo kyhi vy _ b) kzlo kzhi vz _ c =>
    mkNode cmp .red
      (mkNode cmp .black l klo khi v a)
      kylo kyhi vy
      (balance2 cmp b kzlo kzhi vz (setRed c))
  | l, klo, khi, v, r => mkNode cmp .red l klo khi v r  -- unreachable

def balRight (cmp : α → α → Ordering) :
    IntervalNode α β → α → α → β → IntervalNode α β → IntervalNode α β
  | l, klo, khi, v, node .red b kylo kyhi vy _ c =>
    mkNode cmp .red l klo khi v (mkNode cmp .black b kylo kyhi vy c)
  | node .black a kxlo kxhi vx _ b, klo, khi, v, r =>
    balance1 cmp (mkNode cmp .red a kxlo kxhi vx b) klo khi v r
  | node .red a kxlo kxhi vx _ (node .black b kylo kyhi vy _ c), klo, khi, v, r =>
    mkNode cmp .red
      (balance1 cmp (setRed a) kxlo kxhi vx b)
      kylo kyhi vy
      (mkNode cmp .black c klo khi v r)
  | l, klo, khi, v, r => mkNode cmp .red l klo khi v r  -- unreachable

def appendTrees (cmp : α → α → Ordering) :
    IntervalNode α β → IntervalNode α β → IntervalNode α β
  | leaf, x => x
  | x, leaf => x
  | node .red a kxlo kxhi vx _ b, node .red c kylo kyhi vy _ d =>
    match appendTrees cmp b c with
    | node .red b' kzlo kzhi vz _ c' =>
      mkNode cmp .red
        (mkNode cmp .red a kxlo kxhi vx b') kzlo kzhi vz
        (mkNode cmp .red c' kylo kyhi vy d)
    | bc =>
      mkNode cmp .red a kxlo kxhi vx (mkNode cmp .red bc kylo kyhi vy d)
  | node .black a kxlo kxhi vx _ b, node .black c kylo kyhi vy _ d =>
    match appendTrees cmp b c with
    | node .red b' kzlo kzhi vz _ c' =>
      mkNode cmp .red
        (mkNode cmp .black a kxlo kxhi vx b') kzlo kzhi vz
        (mkNode cmp .black c' kylo kyhi vy d)
    | bc =>
      balLeft cmp a kxlo kxhi vx (mkNode cmp .black bc kylo kyhi vy d)
  | x, node .red b kxlo kxhi vx _ c =>
    mkNode cmp .red (appendTrees cmp x b) kxlo kxhi vx c
  | node .red a kxlo kxhi vx _ b, y =>
    mkNode cmp .red a kxlo kxhi vx (appendTrees cmp b y)
termination_by x y => x.size + y.size

@[specialize] def del (cmp : α → α → Ordering) (lo hi : α) :
    IntervalNode α β → IntervalNode α β
  | leaf => leaf
  | node _ l klo khi kv _ r =>
    match cmpInterval cmp lo hi klo khi with
    | .lt =>
      if l.isBlack
      then balLeft  cmp (del cmp lo hi l) klo khi kv r
      else mkNode cmp .red (del cmp lo hi l) klo khi kv r
    | .gt =>
      if r.isBlack
      then balRight cmp l klo khi kv (del cmp lo hi r)
      else mkNode cmp .red l klo khi kv (del cmp lo hi r)
    | .eq => appendTrees cmp l r

@[specialize] def erase (cmp : α → α → Ordering) (lo hi : α)
    (t : IntervalNode α β) : IntervalNode α β :=
  (del cmp lo hi t).setBlack

-- ---------------------------------------------------------------------------
-- Point lookup
-- ---------------------------------------------------------------------------

@[specialize] def find? (cmp : α → α → Ordering) (lo hi : α) :
    IntervalNode α β → Option β
  | leaf => none
  | node _ l klo khi kv _ r =>
    match cmpInterval cmp lo hi klo khi with
    | .lt => find? cmp lo hi l
    | .gt => find? cmp lo hi r
    | .eq => some kv

@[inline] def contains (cmp : α → α → Ordering) (lo hi : α) (t : IntervalNode α β) : Bool :=
  (find? cmp lo hi t).isSome

-- ---------------------------------------------------------------------------
-- Traversal
-- ---------------------------------------------------------------------------

@[specialize] def fold (f : σ → α → α → β → σ) :
    (init : σ) → IntervalNode α β → σ
  | s, leaf              => s
  | s, node _ l lo hi v _ r => fold f (f (fold f s l) lo hi v) r

-- Fold right-to-left; useful for building lists in O(n) via cons.
@[specialize] def revFold (f : σ → α → α → β → σ) :
    (init : σ) → IntervalNode α β → σ
  | s, leaf              => s
  | s, node _ l lo hi v _ r => revFold f (f (revFold f s r) lo hi v) l

@[specialize] def forM [Monad m] (f : α → α → β → m Unit) :
    IntervalNode α β → m Unit
  | leaf              => pure ()
  | node _ l lo hi v _ r => do forM f l; f lo hi v; forM f r

@[inline] protected def forIn [Monad m]
    (t : IntervalNode α β) (init : σ)
    (f : α × α × β → σ → m (ForInStep σ)) : m σ := do
  let rec @[specialize] visit : IntervalNode α β → σ → m (ForInStep σ)
    | leaf, s => return .yield s
    | node _ l lo hi v _ r, s => do
      match ← visit l s with
      | res@(.done _) => return res
      | .yield s =>
        match ← f (lo, hi, v) s with
        | res@(.done _) => return res
        | .yield s => visit r s
  match ← visit t init with
  | .done s  => pure s
  | .yield s => pure s

-- ---------------------------------------------------------------------------
-- Interval queries
-- ---------------------------------------------------------------------------

/-- Fold over every `[a, b]` in the subtree that **overlaps** `[qlo, qhi]`
(i.e., `a ≤ qhi ∧ b ≥ qlo`).

Pruning: if the subtree's `maxHi < qlo`, no interval in it can reach `qlo`, so skip.
If `lo > qhi`, the right sub-tree (all `lo' ≥ lo > qhi`) can never overlap, so skip. -/
@[specialize] def foldOverlapping (cmp : α → α → Ordering) (f : σ → α → α → β → σ)
    (qlo qhi : α) : (init : σ) → IntervalNode α β → σ
  | s, leaf => s
  | s, node _ l lo hi v maxHi r =>
    if cmp maxHi qlo == .lt then s   -- prune: all hi < qlo
    else
      let s := foldOverlapping cmp f qlo qhi s l
      let s := if cmp lo qhi != .gt && cmp hi qlo != .lt then f s lo hi v else s
      if cmp lo qhi == .gt then s    -- right subtree has lo' ≥ lo > qhi, skip
      else foldOverlapping cmp f qlo qhi s r

/-- Fold over every `[a, b]` in the subtree that **contains** `[qlo, qhi]`
(i.e., `a ≤ qlo ∧ b ≥ qhi`).

Pruning:
- If `maxHi < qhi`: no interval in the subtree has a large enough right endpoint.
- If `lo > qlo`:  all right-subtree intervals also have `lo' ≥ lo > qlo`, so none satisfy
  `a ≤ qlo`; skip the right subtree. -/
@[specialize] def foldContaining (cmp : α → α → Ordering) (f : σ → α → α → β → σ)
    (qlo qhi : α) : (init : σ) → IntervalNode α β → σ
  | s, leaf => s
  | s, node _ l lo hi v maxHi r =>
    if cmp maxHi qhi == .lt then s   -- prune: no hi ≥ qhi anywhere in subtree
    else
      let s := foldContaining cmp f qlo qhi s l
      let s := if cmp lo qlo != .gt && cmp hi qhi != .lt then f s lo hi v else s
      if cmp lo qlo == .gt then s    -- lo > qlo ⟹ right subtree also fails a ≤ qlo
      else foldContaining cmp f qlo qhi s r

/-- Fold over every `[a, b]` in the subtree that is **contained in** `[qlo, qhi]`
(i.e., `a ≥ qlo ∧ b ≤ qhi`).

Pruning using BST order on `lo`:
- If `lo > qhi`:  current and right subtree all have `lo' ≥ lo > qhi`, and since valid
  intervals have `lo' ≤ hi'`, we get `hi' ≥ lo' > qhi`; none fit.  Only recurse left.
- If `lo < qlo`:  all left-subtree `lo' ≤ lo < qlo` fail `a ≥ qlo`.  Only recurse right. -/
@[specialize] def foldContainedIn (cmp : α → α → Ordering) (f : σ → α → α → β → σ)
    (qlo qhi : α) : (init : σ) → IntervalNode α β → σ
  | s, leaf => s
  | s, node _ l lo hi v _ r =>
    if cmp lo qhi == .gt then
      -- current.lo > qhi: current fails; right sub-tree also fails; only check left
      foldContainedIn cmp f qlo qhi s l
    else if cmp lo qlo == .lt then
      -- current.lo < qlo: current fails; left sub-tree (all lo' ≤ lo < qlo) also fails
      foldContainedIn cmp f qlo qhi s r
    else
      -- qlo ≤ lo ≤ qhi; check both subtrees and current node
      let s := foldContainedIn cmp f qlo qhi s l
      let s := if cmp hi qhi != .gt then f s lo hi v else s
      foldContainedIn cmp f qlo qhi s r

end IntervalNode

-- ---------------------------------------------------------------------------
-- Public API: IntervalMap
-- ---------------------------------------------------------------------------

/-- A map from closed intervals `[lo, hi]` over an ordered type `α` to values of type `β`.

Implemented as a red-black BST keyed by `(lo, hi)` (lexicographic order), augmented with
`maxHi` (the maximum right endpoint in each subtree).  This enables efficient pruning in
interval queries.

**Complexity**
- `insert`, `erase`, `find?`, `contains`: O(log n)
- `findAllOverlapping`, `findAllContaining`, `findAllContainedIn`: O(log n + k)
- `findSmallestContaining`: O(log n + k + k²) where k = |`findAllContaining`|

All intervals are treated as **closed**: `[lo, hi]` contains both endpoints.  Queries give
correct results for any comparator `cmp`; however, for the tree invariant to hold, `cmp` should
be a total order.

Use `IntervalSet α cmp` when no per-interval values are needed. -/
@[expose] def IntervalMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) :
    Type (max u v) :=
  IntervalNode α β

@[inline] def mkIntervalMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) :
    IntervalMap α β cmp :=
  .leaf

namespace IntervalMap

variable {α : Type u} {β : Type v} {σ : Type w} {cmp : α → α → Ordering}

/-- The empty interval map. -/
@[inline] def empty : IntervalMap α β cmp := .leaf

instance : EmptyCollection (IntervalMap α β cmp) := ⟨empty⟩
instance : Inhabited      (IntervalMap α β cmp) := ⟨∅⟩

/-- Number of intervals in the map. -/
@[inline] def size (t : IntervalMap α β cmp) : Nat :=
  IntervalNode.size t

/-- `true` iff the map contains no intervals. -/
@[inline] def isEmpty (t : IntervalMap α β cmp) : Bool :=
  match t with | .leaf => true | _ => false

/-- Insert `[lo, hi]` with value `v`.  If the interval is already present its value is updated. -/
@[inline] def insert (t : IntervalMap α β cmp) (lo hi : α) (v : β) : IntervalMap α β cmp :=
  IntervalNode.insert cmp lo hi v t

/-- Remove `[lo, hi]` from the map (no-op if absent). -/
@[inline] def erase (t : IntervalMap α β cmp) (lo hi : α) : IntervalMap α β cmp :=
  IntervalNode.erase cmp lo hi t

/-- Return the value associated with `[lo, hi]`, or `none` if absent. -/
@[inline] def find? (t : IntervalMap α β cmp) (lo hi : α) : Option β :=
  IntervalNode.find? cmp lo hi t

/-- `true` iff `[lo, hi]` is in the map. -/
@[inline] def contains (t : IntervalMap α β cmp) (lo hi : α) : Bool :=
  IntervalNode.contains cmp lo hi t

/-- Fold over `(lo, hi, v)` entries in ascending lexicographic order of `(lo, hi)`. -/
@[inline] def fold (f : σ → α → α → β → σ) (init : σ) (t : IntervalMap α β cmp) : σ :=
  IntervalNode.fold f init t

/-- Execute `f lo hi v` for each entry in ascending order. -/
@[inline] def forM [Monad m] (f : α → α → β → m Unit) (t : IntervalMap α β cmp) : m Unit :=
  IntervalNode.forM f t

instance [Monad m] : ForIn m (IntervalMap α β cmp) (α × α × β) where
  forIn t init f := IntervalNode.forIn t init f

/-- Convert to a list of `(lo, hi, v)` triples in ascending order. -/
def toList (t : IntervalMap α β cmp) : List (α × α × β) :=
  -- revFold + cons gives O(n) list building
  IntervalNode.revFold (fun acc lo hi v => (lo, hi, v) :: acc) [] t

/-- Convert to an array of `(lo, hi, v)` triples in ascending order. -/
def toArray (t : IntervalMap α β cmp) : Array (α × α × β) :=
  IntervalNode.fold (fun acc lo hi v => acc.push (lo, hi, v)) #[] t

/-- Build an `IntervalMap` from a list of `(lo, hi, v)` triples. -/
def ofList (l : List (α × α × β)) : IntervalMap α β cmp :=
  l.foldl (fun t (lo, hi, v) => t.insert lo hi v) empty

-- ---- Interval queries ----

/-- All intervals `[a, b]` in the map that **overlap** `[qlo, qhi]`
(i.e., `a ≤ qhi ∧ b ≥ qlo`).  Returns a list in unspecified order. -/
def findAllOverlapping (t : IntervalMap α β cmp) (qlo qhi : α) : List (α × α × β) :=
  IntervalNode.foldOverlapping cmp
    (fun acc lo hi v => (lo, hi, v) :: acc) qlo qhi [] t

/-- All intervals `[a, b]` in the map that **contain** `[qlo, qhi]`
(i.e., `a ≤ qlo ∧ b ≥ qhi`).  Returns a list in unspecified order. -/
def findAllContaining (t : IntervalMap α β cmp) (qlo qhi : α) : List (α × α × β) :=
  IntervalNode.foldContaining cmp
    (fun acc lo hi v => (lo, hi, v) :: acc) qlo qhi [] t

/-- All intervals `[a, b]` in the map that are **contained in** `[qlo, qhi]`
(i.e., `a ≥ qlo ∧ b ≤ qhi`).  Returns a list in unspecified order. -/
def findAllContainedIn (t : IntervalMap α β cmp) (qlo qhi : α) : List (α × α × β) :=
  IntervalNode.foldContainedIn cmp
    (fun acc lo hi v => (lo, hi, v) :: acc) qlo qhi [] t

/-- The **minimal-under-containment** subset of `findAllContaining t qlo qhi`.

An interval `[a, b]` is included iff it contains `[qlo, qhi]` and no other interval
`[a', b']` in the map satisfies `a ≤ a' ≤ qlo` and `qhi ≤ b' ≤ b` with at least one
inequality strict (i.e., no proper sub-interval of `[a, b]` also contains `[qlo, qhi]`).

Time: O(log n + k²) where k = |`findAllContaining`|. -/
def findSmallestContaining (t : IntervalMap α β cmp) (qlo qhi : α) : List (α × α × β) :=
  let all := t.findAllContaining qlo qhi
  all.filter fun (a, b, _) =>
    -- Keep [a, b] unless some [a', b'] in `all` is strictly tighter:
    --   a ≤ a' (tighter lower bound) ∧ b' ≤ b (tighter upper bound) ∧ (a < a' ∨ b' < b)
    all.all fun (a', b', _) =>
      !(cmp a a' != .gt && cmp b' b != .gt && (cmp a a' == .lt || cmp b' b == .lt))

end IntervalMap

-- ---------------------------------------------------------------------------
-- Convenience alias: IntervalSet
-- ---------------------------------------------------------------------------

/-- A set of closed intervals `[lo, hi]` over an ordered type `α`.
A thin alias for `IntervalMap α Unit cmp`. -/
@[expose] abbrev IntervalSet (α : Type u) (cmp : α → α → Ordering) :=
  IntervalMap α Unit cmp

namespace IntervalSet

variable {α : Type u} {cmp : α → α → Ordering}

/-- The empty set. -/
@[inline] def empty : IntervalSet α cmp := IntervalMap.empty

/-- Insert `[lo, hi]`. -/
@[inline] def insert (t : IntervalSet α cmp) (lo hi : α) : IntervalSet α cmp :=
  IntervalMap.insert t lo hi ()

/-- Remove `[lo, hi]` (no-op if absent). -/
@[inline] def erase (t : IntervalSet α cmp) (lo hi : α) : IntervalSet α cmp :=
  IntervalMap.erase t lo hi

/-- `true` iff `[lo, hi]` is in the set. -/
@[inline] def contains (t : IntervalSet α cmp) (lo hi : α) : Bool :=
  IntervalMap.contains t lo hi

/-- Convert to a list of `(lo, hi)` pairs in ascending order. -/
def toList (t : IntervalSet α cmp) : List (α × α) :=
  IntervalNode.revFold (fun acc lo hi _ => (lo, hi) :: acc) [] t

/-- All intervals overlapping `[qlo, qhi]`. -/
def findAllOverlapping (t : IntervalSet α cmp) (qlo qhi : α) : List (α × α) :=
  IntervalNode.foldOverlapping cmp
    (fun acc lo hi _ => (lo, hi) :: acc) qlo qhi [] t

/-- All intervals containing `[qlo, qhi]`. -/
def findAllContaining (t : IntervalSet α cmp) (qlo qhi : α) : List (α × α) :=
  IntervalNode.foldContaining cmp
    (fun acc lo hi _ => (lo, hi) :: acc) qlo qhi [] t

/-- Smallest (minimal under containment) intervals containing `[qlo, qhi]`. -/
def findSmallestContaining (t : IntervalSet α cmp) (qlo qhi : α) : List (α × α) :=
  (IntervalMap.findSmallestContaining t qlo qhi).map fun (a, b, _) => (a, b)

/-- All intervals contained in `[qlo, qhi]`. -/
def findAllContainedIn (t : IntervalSet α cmp) (qlo qhi : α) : List (α × α) :=
  IntervalNode.foldContainedIn cmp
    (fun acc lo hi _ => (lo, hi) :: acc) qlo qhi [] t

end IntervalSet

end Lean
