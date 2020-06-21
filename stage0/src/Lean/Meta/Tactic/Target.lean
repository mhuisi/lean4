/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- newTarget` using an equality proof `eqProof : target = newTarget`.
  It assumes `eqProof` has type `target = newTarget` -/
def replaceTargetEq (mvarId : MVarId) (newTarget : Expr) (eqProof : Expr) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `replaceTarget;
  tag      ← getMVarTag mvarId;
  newMVar  ← mkFreshExprSyntheticOpaqueMVar newTarget tag;
  target   ← getMVarType mvarId;
  u        ← getLevel target;
  eq       ← mkEq target newTarget;
  newProof ← mkExpectedTypeHint eqProof eq;
  let newVal := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, newTarget, eqProof, newMVar];
  assignExprMVar mvarId newMVar;
  pure newMVar.mvarId!

/--
  Convert the given goal `Ctx | target` into `Ctx |- newTarget`. It assumes the goals are definitionally equal.
  We use the proof term
  ```
  @id target newMVar
  ```
  to create a checkpoint. -/
def replaceTargetDefEq (mvarId : MVarId) (newTarget : Expr) : MetaM MVarId :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `change;
  target  ← getMVarType mvarId;
  if target == newTarget then pure mvarId
  else do
    tag     ← getMVarTag mvarId;
    newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag;
    newVal  ← mkExpectedTypeHint newMVar target;
    assignExprMVar mvarId newMVar;
    pure newMVar.mvarId!

end Meta
end Lean
