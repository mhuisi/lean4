import Lean

/-!
Tests that the elaborator emits `ChoiceResolutionInfo` nodes into the `InfoTree` that identify
which alternative of a `choice` node (ambiguous syntax) was picked during elaboration of terms,
tactics, and commands.

Note: the later-declared syntax comes first in the `choice` node, so the `B` variants below are
the alternatives at index 0.
-/

structure Foo where
  abc : Nat
  foo : Nat

-- Term-level choice node between overloaded syntax: the alternative that fails to elaborate
-- (`termB`) is discarded and the succeeding one is recorded as picked.
syntax (name := termA) "myterm" : term
syntax (name := termB) "myterm" : term

open Lean Elab Term in
@[term_elab termA] def elabTermA : TermElab := fun _ _ => return Lean.mkNatLit 0

open Lean Elab Term in
@[term_elab termB] def elabTermB : TermElab := fun _ _ => throwError "termB failed"

-- Tactic-level and command-level choice nodes: the elaborator commits to the first alternative
-- accepted by `evalTactic`/`elabCommand`, which is recorded as picked.
macro (name := tacA) "mytac" : tactic => `(tactic| exact 41)
macro (name := tacB) "mytac" : tactic => `(tactic| exact 42)

macro (name := cmdA) "mycmd" : command => `(#eval "cmdA")
macro (name := cmdB) "mycmd" : command => `(#eval "cmdB")

-- Overloaded infix notation for the pattern-level choice node tests below.
inductive MySeq where
  | nil
  | cons (x : Nat) (s : MySeq)

infixr:67 " ::: " => MySeq.cons
infixr:67 " ::: " => List.cons

set_option trace.Elab.info true

-- Term-level choice node resolved by type: `{ abc, foo }` is ambiguous between the set-like
-- `«term{_}»` notation and `Term.structInst`; elaboration picks the structure instance.
def x (abc foo : Nat) : Foo := { abc, foo }

#check (myterm : Nat)

example : Nat := by mytac

mycmd

-- Pattern-level choice node: the pattern elaborator rewrites the alternatives of the `choice`
-- node for the overloaded `:::` notation into explicit constructor applications before the
-- elaborator resolves it. The recorded alternative index remains valid for the original
-- `choice` node.
def head? (xs : List Nat) : Option Nat :=
  match xs with
  | x ::: _ => some x
  | _ => none

-- Pattern-level choice node with a `Term.structInst` alternative: the pattern elaborator
-- discards all non-`structInst` alternatives, but replaces them with `missing` instead of
-- removing them, so the recorded alternative index remains valid for the original `choice` node
-- (and the number of alternatives reported below matches the original `choice` node).
def y' (v : Foo) : Nat :=
  match v with
  | { abc, foo } => abc + foo
