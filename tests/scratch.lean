module

prelude
import Lean

def foo (stx : Lean.TSyntax ``Lean.Parser.Term.letIdBinder)
    : Lean.TSyntax [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
  match stx with
  | `(Lean.Parser.Term.letIdBinder| $id:ident) => id
  | `(Lean.Parser.Term.letIdBinder| $hole:hole) => hole
  | `(Lean.Parser.Term.letIdBinder| $bracketedBinder:bracketedBinder) => bracketedBinder
  | _ => sorry

abbrev foobar (a : Nat × Nat × Nat × Nat × Nat) (b c d : Nat) : Nat := match 0, 0 with
| 0, 0
| 1, 1 => 0
| n, _ => n

#synth Lean.ToJson (Option Nat)

@[simp] example : Nat := 1

@[simp]
example (a
    : Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat
      × Nat)
    : Nat → Nat → Nat → Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
  | 0, 0,
      0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 =>
    sorry
  | n, _, _ =>
    sorry

where

  foobar : Nat := 1

  barfoo : Nat := 3

structure Bar where
  a : Nat
  b : Nat

structure Foo where
  a : Bar
  b : Nat

set_option linter.missingFormatter true

abbrev foob : Foo where
  aaaaaaaaaaaaaaaaaaaaaa[
        000000000000000000000000000000000000000000000000000000000000000000000000000000
      ]
      .aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
      .bbbbb
      : Naaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaat :=
    111111111111

open Lean.Fmt
