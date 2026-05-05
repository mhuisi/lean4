module

prelude
import Lean

/-- Internal representation of `Void` in the compiler. -/
unsafe axiom lcVoid' : Type

@[simp]
abbrev Eq.ndrec'.{u1, u2}
    {α : Sort u2} {a : α} {motive : α → Sort u1}
    (m : motive a)
    {b : α}
    (h : Eq a b)
    : motive b := h.rec m

/-- asdf -/
@[inline] def id' {α : Sort u} (a : α) : α := aa

/-- Alias for `Or.inl`. -/
theorem Or.intro_left' (b : Prop) (h : a) : Or a b := Or.inl h

def foo : Nat → Nat → Nat
  | 0, 0 => 0
  | n, mmmmm => n + mmmmm
