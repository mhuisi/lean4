import Lean.Data.Fmt

open Lean
open Lean.Data
open Lean.Fmt

def printSyntaxKinds : MetaM Unit := do
  let env ← getEnv
  let kinds := Parser.parserExtension.getState env |>.kinds.toArray.map (·.1) |>.qsort Name.lt
  for kind in kinds do
    IO.println kind

@[fmt «term_+_»]
def fmt1 : Fmt
  | `($a +%$tk $b) => do
    let a ← fmt a
    let b ← fmt b
    let sum :=  fmt!"{a.nested}".append (Doc.nested fmt!"{Doc.nl}{tk.getAtomVal} {b.nested}")
    return .maybeFlattened sum
  | _ => throw ()

@[fmt num]
def fmt2 : Fmt
  | `($n:num) => do
    let Syntax.atom _ val := n.raw.ifNode (fun n => n.getArg 0) (fun _ => n.raw)
      | throw ()
    return .text val
  | _ => throw ()

@[fmt Lean.Parser.Term.paren]
def fmt3 : Fmt
  | `(($t)) => do
    let t ← fmt t
    return fmt!"({t})"
  | _ => throw ()


def test : MetaM Unit := do
  let stx ← `(1 + 2 + 3 + 33333333333333333 + 4)
  let .ok r := fmt stx |>.run { env := ← getEnv }
    | panic "error"
  let some r := format? r 20
    | panic "error 2"
  IO.println r

#eval test
