/-!
Tests for the formatters of the `guard_*` tactics, conv tactics, and commands (`fmtGuardExpr`,
`fmtGuardExprConv`, `fmtGuardExprCmd`, `fmtGuardTarget`, `fmtGuardTargetConv`, `fmtGuardHyp`,
`fmtGuardHypConv`, `fmtGuardCmd`) and of their matching specifiers (`fmtGuardColon`,
`fmtGuardColonEq`, `fmtGuardEqual`): all four transparency variants of each specifier, `guard_hyp`
with and without each of its optional components, and forms long enough to be broken across lines.
-/

def compress (xs : List Nat) : List Nat :=
  xs.filter (· != 0)

def decompress (xs : List Nat) (padding : Nat) : List Nat :=
  xs ++ List.replicate padding 0

/-! ## `guard_expr` -/

example : True := by
  guard_expr 2 + 2 = 4
  trivial

example (n : Nat) : True := by
  guard_expr n + 0 =~ n
  trivial

example (n : Nat) : True := by
  guard_expr n * 1 =ₛ n * 1
  trivial

example (f : Nat → Nat) : True := by
  guard_expr (fun x => f x) =ₐ (fun y => f y)
  trivial

example (xs : List Nat) : True := by
  guard_expr compress (decompress xs 4) =~ compress (decompress xs 4)
  trivial

example (buckets : List Nat) (padding : Nat) : True := by
  guard_expr compress (decompress (compress buckets) padding) =ₛ
    compress (decompress (compress buckets) padding)
  trivial

example (elements : List Nat) : True := by
  guard_expr (decompress (compress elements) (elements.length - (compress elements).length)).length =~
    (decompress (compress elements) (elements.length - (compress elements).length)).length
  trivial

/-! ## `guard_expr` in `conv` -/

example (n : Nat) : n + 0 = n := by
  conv =>
    guard_expr n + 0 =~ n
    rw [Nat.add_zero]

example (xs : List Nat) (padding : Nat) : decompress xs padding = decompress xs padding := by
  conv =>
    guard_expr decompress xs padding =ₐ decompress xs padding

example (elements : List Nat) : compress elements = compress elements := by
  conv =>
    guard_expr compress (decompress (compress elements) elements.length) =ₛ
      compress (decompress (compress elements) elements.length)

/-! ## `guard_target` -/

example : 2 + 2 = 4 := by
  guard_target = 2 + 2 = 4
  rfl

example (n : Nat) : n + 0 = n := by
  guard_target =~ n = n
  simp

example (xs : List Nat) : compress xs = compress xs := by
  guard_target =ₛ compress xs = compress xs
  rfl

example (f : Nat → Nat) : (fun x => f x) = fun y => f y := by
  guard_target =ₐ (fun x => f x) = fun z => f z
  rfl

example (elements : List Nat) (padding : Nat) :
    compress (decompress (compress elements) padding) = compress elements := by
  guard_target =ₛ compress (decompress (compress elements) padding) = compress elements
  simp [compress, decompress]

example (elements : List Nat) (padding : Nat) :
    (decompress (compress elements) padding).length = (compress elements).length + padding := by
  guard_target =~
    (decompress (compress elements) padding).length = (compress elements).length + padding
  simp [decompress]

/-! ## `guard_target` in `conv` -/

example (n : Nat) : n + 0 = n := by
  conv =>
    guard_target = n + 0 = n
    rw [Nat.add_zero]

example (xs : List Nat) : compress xs = compress xs := by
  conv =>
    guard_target =ₛ compress xs = compress xs

example (elements : List Nat) (padding : Nat) :
    compress (decompress (compress elements) padding) =
      compress (decompress (compress elements) padding) := by
  conv =>
    guard_target =ₐ
      compress (decompress (compress elements) padding) =
        compress (decompress (compress elements) padding)

/-! ## `guard_hyp` with a type only -/

example (n : Nat) : True := by
  guard_hyp n : Nat
  trivial

example (xs : List Nat) : True := by
  guard_hyp xs :~ List Nat
  trivial

example (h : 2 + 2 = 4) : True := by
  guard_hyp h :ₛ 2 + 2 = 4
  trivial

example (f : Nat → Nat) (h : ∀ x, f x = x) : True := by
  guard_hyp h :ₐ ∀ y, f y = y
  trivial

example (roundTrip : ∀ (elements : List Nat) (padding : Nat),
    compress (decompress (compress elements) padding) = compress elements) : True := by
  guard_hyp roundTrip :ₛ ∀ (elements : List Nat) (padding : Nat),
    compress (decompress (compress elements) padding) = compress elements
  trivial

/-! ## `guard_hyp` with a value only -/

example (n : Nat) : True := by
  let successor := n + 1
  guard_hyp successor := n + 1
  trivial

example (xs : List Nat) : True := by
  let compressed := compress xs
  guard_hyp compressed :=~ compress xs
  trivial

example (xs : List Nat) : True := by
  let padded := decompress xs 3
  guard_hyp padded :=ₛ decompress xs 3
  trivial

example (f : Nat → Nat) : True := by
  let pointwise := fun x => f x
  guard_hyp pointwise :=ₐ fun y => f y
  trivial

example (elements : List Nat) (padding : Nat) : True := by
  let roundTripped := compress (decompress (compress elements) (padding + elements.length))
  guard_hyp roundTripped :=ₛ
    compress (decompress (compress elements) (padding + elements.length))
  trivial

/-! ## `guard_hyp` with both a type and a value -/

example (n : Nat) : True := by
  let successor := n + 1
  guard_hyp successor : Nat := n + 1
  trivial

example (xs : List Nat) : True := by
  let compressed := compress xs
  guard_hyp compressed :ₛ List Nat :=~ compress xs
  trivial

example (elements : List Nat) : True := by
  let compressed := compress elements
  guard_hyp compressed :~ List Nat :=ₐ compress elements
  trivial

example (elements : List Nat) (padding : Nat) : True := by
  let roundTripped := decompress (compress elements) padding
  guard_hyp roundTripped : List Nat := decompress (compress elements) padding
  trivial

example (elements : List Nat) (padding : Nat) : True := by
  let roundTripped := compress (decompress (compress elements) (padding + elements.length))
  guard_hyp roundTripped :ₛ List Nat :=ₛ
    compress (decompress (compress elements) (padding + elements.length))
  trivial

/-! ## `guard_hyp` without a type or a value -/

example (n : Nat) : True := by
  guard_hyp n
  trivial

/-! ## `guard_hyp` in `conv` -/

example (n : Nat) : n + 0 = n := by
  conv =>
    guard_hyp n : Nat
    rw [Nat.add_zero]

example (elements : List Nat) : compress elements = compress elements := by
  conv =>
    guard_hyp elements :ₛ List Nat

example (elements : List Nat) (padding : Nat) :
    decompress elements padding = decompress elements padding := by
  conv =>
    guard_hyp padding :~ Nat

/-! ## `#guard_expr` -/

#guard_expr 2 + 2 = 4

#guard_expr [1, 2, 3].length =~ 3

#guard_expr compress [0, 1, 0, 2] =ₛ compress [0, 1, 0, 2]

#guard_expr (fun (xs : List Nat) => compress xs) =ₐ fun (ys : List Nat) => compress ys

#guard_expr compress (decompress (compress [1, 0, 2, 0, 3]) 5) =ₛ
  compress (decompress (compress [1, 0, 2, 0, 3]) 5)

/-! ## `#guard` -/

#guard 2 + 2 == 4

#guard compress [0, 1, 0, 2] == [1, 2]

#guard (decompress (compress [1, 0, 2, 0, 3]) 4).length == (compress [1, 0, 2, 0, 3]).length + 4

#guard decompress (compress [1, 0, 2, 0, 3, 0, 4, 0, 5]) 6 ==
  [1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0]
