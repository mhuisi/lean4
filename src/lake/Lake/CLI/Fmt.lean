/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
import Lake.Formatters -- shake: keep (registers Lake's formatters)
import Lean.Fmt
import Lean.Language.Lean
import Lean.Elab.Import
public import Init.System.IO
public import Init.System.FilePath

open System Lean

namespace Lake.Fmt

/--
Walks the chain of `CommandParsedSnapshot`s rooted at `snap` and returns the syntax trees of all
commands, or `none` if any of them recorded parser-level error diagnostics.
Forces command parsing, but not elaboration.
-/
private partial def collectParsedCmds? (snap : Language.Lean.CommandParsedSnapshot)
    (cmds : Array Syntax := #[]) : Option (Array Syntax) :=
  if snap.diagnostics.msgLog.hasErrors then
    none
  else
    let cmds := cmds.push snap.stx
    match snap.nextCmdSnap? with
    | some next => collectParsedCmds? next.get cmds
    | none => some cmds

/--
Format `file` using the Lean auto-formatter.
Writes the formatted result back to `file`.
-/
public def fmtFile (file : FilePath) : IO UInt32 := do
  let contents ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext contents file.toString
  unsafe enableInitializersExecution
  let opts := Elab.inServer.set {} true
  -- let opts := opts.setBool `interpreter.prefer_native false
  -- Note: We must not set `internal.cmdlineSnapshots` here, as the formatter needs the
  -- information that it strips from the snapshot tree (e.g. info trees).
  let setup headerStx :=
    return .ok {
      mainModuleName := .anonymous
      isModule := headerStx.isModule
      imports := headerStx.imports
      opts
    }
  let initialSnap ← Language.Lean.process setup none { inputCtx with }
  match ← Fmt.fileMain initialSnap with
  | .error err =>
    IO.eprintln s!"error: {file}: {err}"
    return 1
  | .ok formatted =>
    IO.FS.writeFile file formatted
    return 0
