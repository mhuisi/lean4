import Lean

open Lean
open Lean.Data
open Lean.Fmt

def printSyntaxKinds : MetaM Unit := do
  let env ← getEnv
  let kinds := Parser.parserExtension.getState env |>.kinds.toArray.map (·.1) |>.qsort Name.lt
  for kind in kinds do
    IO.println kind

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

deriving instance Repr for ParserDescr

infixl:80 (name := AAA) " AAA " => Nat.add
infixr:80 (name := BBB) " BBB " => Nat.add
infix:80 (name := CCC) " CCC " => Nat.add

def foo : MetaM Unit := do
  dbg_trace repr «AAA»
  dbg_trace repr «BBB»
  dbg_trace repr «BBB»

#eval foo

def s := "
#eval 111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111 + 1 + 1


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
  let r ← IO.ofExcept <| Fmt.main (← getEnv) (← getOptions) stx
  IO.println r

#eval test

set_option pp.raw true
--set_option pp.raw.showInfo true
set_option trace.Elab.command true
