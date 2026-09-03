/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Std.Tactic.BVDecide.LRAT.Internal.Entails
import Init.Data

namespace Lean.Fmt

@[builtin_infix_fmt Std.Tactic.BVDecide.LRAT.Internal.«term_⊭_»]
public def fmtNotEntails : Fmt.InfixOperation :=
  { sparse := true, precs? := some { prec := 25, lhsPrec := 25, rhsPrec := 30 } }
