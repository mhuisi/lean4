import Lean

open Lean
open Lean.Data
open Lean.Fmt

inductive Lean.Syntax.InfixOperationAssociativity where
  | left
  | right

inductive Lean.Syntax.InfixOperatorChainLink where
  | operand (stx : Syntax)
  | operator (stx : Syntax)

instance : ToString Lean.Syntax.InfixOperatorChainLink where
  toString
    | .operand stx => toString stx
    | .operator stx => toString stx

variable (assoc : Syntax.InfixOperationAssociativity) in
partial def Lean.Syntax.infixOperatorChain (stx : Syntax) : Array InfixOperatorChainLink := Id.run do
  if stx.getNumArgs != 3 then
    return #[.operand stx]
  let left := stx[0]
  let op := stx[1]
  let right := stx[2]
  if ! op.isAtom then
    return #[.operand stx]
  let leftChain :=
    if assoc matches .left then
      infixOperatorChain left
    else
      #[.operand left]
  let rightChain :=
    if assoc matches .right then
      infixOperatorChain right
    else
      #[.operand right]
  return leftChain ++ #[.operator op] ++ rightChain

def printSyntaxKinds : MetaM Unit := do
  let env ← getEnv
  let kinds := Parser.parserExtension.getState env |>.kinds.toArray.map (·.1) |>.qsort Name.lt
  for kind in kinds do
    IO.println kind

def fmtInfixOperator (assoc : Syntax.InfixOperationAssociativity) : Fmt := fun stx => do
  let chain := stx.infixOperatorChain assoc
    let chain ← chain.mapM fun
      | .operator stx => do
        return nl ++ (← fmt stx) ++ space
      | .operand stx => do
        let operand ← fmt stx
        return nested operand
    let doc := nested <| join chain
    return maybeFlattened doc

@[fmt «term_+_»]
def fmt1 : Fmt := fmtInfixOperator .left

@[fmt «term_-_»]
def fmt4 : Fmt := fmtInfixOperator .left

@[fmt «term_*_»]
def fmt5 : Fmt := fmtInfixOperator .left

@[fmt «term_/_»]
def fmt6 : Fmt := fmtInfixOperator .left

@[fmt Lean.Parser.Term.arrow]
def fmt7 : Fmt := fmtInfixOperator .right

-- @[fmt ident]
-- def fmt8 : Fmt
--   | `($i:ident) =>
--     return .text i.getId.toString
--   | _ =>
--     throw ()


  -- | `($a +%$tk $b) => do
  --   let a ← fmt a
  --   let b ← fmt b
  --   let sum :=  fmt!"{a.nested}".append (Doc.nested fmt!"{Doc.nl}{tk.getAtomVal} {b.nested}")
  --   return .maybeFlattened sum
  -- | _ => throw ()

@[fmt num]
def fmt2 : Fmt
  | stx@`($n:num) => do
    let Syntax.atom _ val := n.raw.ifNode (fun n => n.getArg 0) (fun _ => n.raw)
      | throw ()
    text val stx
  | _ => throw ()

@[fmt Lean.Parser.Term.paren]
def fmt3 : Fmt
  | `((%$lb $t )%$rb) => do
    let lb ← fmt lb
    let t ← fmt t
    let rb ← fmt rb
    return lb ++ t ++ rb
  | _ => throw ()

def test : MetaM Unit := do
  let stx ← `((1111111111111111 + 2) + (3 + 4))
  dbg_trace stx
  let some r := fmt stx |>.run (← getEnv)
    | panic "error"
  let some r := format? r.doc 20
    | panic "error 2"
  IO.println r.rendering

#eval test

#eval 1
  + 1
  +
  -- the third addition
  1
  + 1

-- (1 + 2) + 3
-- => [1, +, 2, +, 3]
-- (((1 + 2) - 3) + 4) + 5

-- (asdf) => eps + asdf
-- asdf: [1, 5] => eps + [1, 5] - 1
-- wohin mappt [0, 6]?
