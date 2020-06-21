/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Module

namespace Lean
namespace Elab

def headerToImports (header : Syntax) : List Import :=
let header  := header.asNode;
let imports := if (header.getArg 0).isNone then [{ module := `Init : Import }] else [];
imports ++ (header.getArg 1).getArgs.toList.map (fun stx =>
  -- `stx` is of the form `(Module.import "import" "runtime"? id)
  let runtime := !(stx.getArg 1).isNone;
  let id      := stx.getIdAt 2;
  { module := id, runtimeOnly := runtime })

def processHeader (header : Syntax) (messages : MessageLog) (inputCtx : Parser.InputContext) (trustLevel : UInt32 := 0) : IO (Environment × MessageLog) :=
catch
  (do env ← importModules (headerToImports header) trustLevel;
      pure (env, messages))
  (fun e => do
     env ← mkEmptyEnvironment;
     let spos := header.getPos.getD 0;
     let pos  := inputCtx.fileMap.toPosition spos;
     pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos }))

def parseImports (input : String) (fileName : Option String := none) : IO (List Import × Position × MessageLog) := do
env ← mkEmptyEnvironment;
let fileName := fileName.getD "<input>";
let inputCtx := Parser.mkInputContext input fileName;
match Parser.parseHeader env inputCtx with
| (header, parserState, messages) => do
  pure (headerToImports header, inputCtx.fileMap.toPosition parserState.pos, messages)

@[export lean_parse_imports]
def parseImportsExport (input : String) (fileName : Option String) : IO (List Import × Position × List Message) := do
(imports, pos, log) ← parseImports input fileName;
pure (imports, pos, log.toList)

@[export lean_print_deps]
def printDeps (deps : List Import) : IO Unit :=
deps.forM $ fun dep => do
  fname ← findOLean dep.module;
  IO.println fname

end Elab
end Lean
