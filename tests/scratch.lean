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

@[fmt num]
def fmt2 : Fmt
  | stx@`($n:num) => do
    let Syntax.atom _ val := n.raw.ifNode (fun n => n.getArg 0) (fun _ => n.raw)
      | throw .partialFormatter
    text val stx
  | _ => throw .partialFormatter

@[fmt Lean.Parser.Term.paren]
def fmt3 : Fmt
  | `((%$lb $t )%$rb) => do
    let lb ← fmt lb
    let t ← fmt t
    let rb ← fmt rb
    return lb ++ t ++ rb
  | _ => throw .partialFormatter

def module := `Lean.Parser.Module.module

@[fmt null]
def fmtNull : Fmt := fun stx => do
  let docs ← stx.getArgs.mapM fmt
  return joinUsing ⟨.nl⟩ docs

@[fmt Lean.Parser.Command.eval]
def fmtEval : Fmt
  | `(#eval%$tk $t) => do
    let tk ← fmt tk
    let t ← fmt t
    return joinUsing ⟨.text " "⟩ #[tk, t]
  | _ => throw .partialFormatter

def s := "
#eval 1 + 1 + 1


-- a
#eval 1
  -- b
  + 111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111 + /- asdf -/ 1 -- c
"

def testParse (env : Environment) (fname contents : String) : IO Syntax := do
  let inputCtx := Parser.mkInputContext contents fname
  let (header, state, messages) ← Parser.parseHeader inputCtx
  let cmds ← Parser.testParseModuleAux env inputCtx state messages #[]
  pure <| mkListNode cmds

def test : MetaM Unit := do
  let env ← getEnv
  let stx ← testParse env "<test>" s
  let r ← IO.ofExcept <| Fmt.main (← getEnv) stx
  IO.println r

#eval test

set_option pp.raw true
--set_option pp.raw.showInfo true
set_option trace.Elab.command true
