/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Parser.Module.Syntax
import Lean.Parser.Module

namespace Lean.Fmt

public def headerKind := ``Parser.Module.header
public def moduleKind := ``Parser.Module.module
public def cmdsKind := `Lean.Parser.Module.cmds

/--
Builds the module syntax that the formatter operates on.

Yields `none` if `cmdStxs` contains a terminal command other than `Lean.Parser.Command.eoi`, i.e.
`#exit` or an `import` after the module header. Command parsing stops at such a command, so the
remainder of the file is missing from `cmdStxs` and formatting the result would delete it.
-/
public def mkModuleSyntax? (headerStx : Syntax) (cmdStxs : Array Syntax) :
    Option Syntax := do
  guard <| cmdStxs.all fun cmdStx =>
    ! Parser.isTerminalCommand cmdStx || cmdStx.isOfKind ``Parser.Command.eoi
  return mkNode moduleKind #[headerStx, mkNode cmdsKind cmdStxs]
