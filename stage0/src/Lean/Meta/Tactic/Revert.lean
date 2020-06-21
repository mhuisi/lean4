/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

def revert (mvarId : MVarId) (fvars : Array FVarId) (preserveOrder : Bool := false) : MetaM (Array FVarId × MVarId) :=
if fvars.isEmpty then pure (fvars, mvarId)
else withMVarContext mvarId $ do
  tag ← getMVarTag mvarId;
  checkNotAssigned mvarId `revert;
  -- Set metavariable kind to natural to make sure `elimMVarDeps` will assign it.
  setMVarKind mvarId MetavarKind.natural;
  e ← finally (elimMVarDeps (fvars.map mkFVar) (mkMVar mvarId) preserveOrder) (setMVarKind mvarId MetavarKind.syntheticOpaque);
  e.withApp $ fun mvar args => do
    setMVarTag mvar.mvarId! tag;
    pure (args.map Expr.fvarId!, mvar.mvarId!)

end Meta
end Lean
