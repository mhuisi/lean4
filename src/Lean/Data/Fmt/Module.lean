/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Parser.Module.Syntax

namespace Lean.Fmt

public def headerKind := ``Parser.Module.header
public def moduleKind := ``Parser.Module.module
public def cmdsKind := `Lean.Parser.Module.cmds

public def mkModuleSyntax (headerStx : Syntax) (cmdStxs : Array Syntax) :
    Syntax :=
  mkNode moduleKind #[headerStx, mkNode cmdsKind cmdStxs]
