/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.LBool
import Lean.Meta.InferType

namespace Lean
namespace Meta

partial def evalNat : Expr → Option Nat
| Expr.lit (Literal.natVal n) _ => pure n
| Expr.mdata _ e _              => evalNat e
| Expr.const `Nat.zero _ _      => pure 0
| e@(Expr.app _ a _)            =>
  let fn    := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if c == `Nat.succ && nargs == 1 then do
      v ← evalNat a; pure $ v+1
    else if c == `Nat.add && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ + v₂
    else if c == `Nat.sub && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ - v₂
    else if c == `Nat.mul && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ * v₂
    else if c == `HasAdd.add && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ + v₂
    else if c == `HasAdd.sub && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ - v₂
    else if c == `HasAdd.mul && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ * v₂
    else if c == `HasOfNat.ofNat && nargs == 3 then
      evalNat (e.getArg! 2)
    else
      none
  | _ => none
| _ => none

/- Quick function for converting `e` into `s + k` s.t. `e` is definitionally equal to `Nat.add s k`. -/
private partial def getOffsetAux : Expr → Bool → Option (Expr × Nat)
| e@(Expr.app _ a _), top =>
  let fn := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if c == `Nat.succ && nargs == 1 then do
      (s, k) ← getOffsetAux a false;
      pure (s, k+1)
    else if c == `Nat.add && nargs == 2 then do
      v      ← evalNat (e.getArg! 1);
      (s, k) ← getOffsetAux (e.getArg! 0) false;
      pure (s, k+v)
    else if c == `HasAdd.add && nargs == 4 then do
      v      ← evalNat (e.getArg! 3);
      (s, k) ← getOffsetAux (e.getArg! 2) false;
      pure (s, k+v)
    else if top then none else pure (e, 0)
  | _ => if top then none else pure (e, 0)
| e, top => if top then none else pure (e, 0)

private def getOffset (e : Expr) : Option (Expr × Nat) :=
getOffsetAux e true

private partial def isOffset : Expr → Option (Expr × Nat)
| e@(Expr.app _ a _) =>
  let fn := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if (c == `Nat.succ && nargs == 1) || (c == `Nat.add && nargs == 2) || (c == `HasAdd.add && nargs == 4) then
      getOffset e
    else none
  | _ => none
| _ => none

private def isNatZero (e : Expr) : Bool :=
match evalNat e with
| some v => v == 0
| _      => false

private def mkOffset (e : Expr) (offset : Nat) : Expr :=
if offset == 0 then e
else if isNatZero e then mkNatLit offset
else mkAppB (mkConst `Nat.add) e (mkNatLit offset)

def isDefEqOffset (s t : Expr) : MetaM LBool :=
let isDefEq (s t) : MetaM LBool := toLBoolM $ isExprDefEqAux s t;
match isOffset s with
| some (s, k₁) => match isOffset t with
  | some (t, k₂) => -- s+k₁ =?= t+k₂
    if k₁ == k₂ then isDefEq s t
    else if k₁ < k₂ then isDefEq s (mkOffset t (k₂ - k₁))
    else isDefEq (mkOffset s (k₁ - k₂)) t
  | none => match evalNat t  with
    | some v₂ => -- s+k₁ =?= v₂
      if v₂ ≥ k₁ then isDefEq s (mkNatLit $ v₂ - k₁) else pure LBool.false
    | none    => pure LBool.undef
| none => match evalNat s with
  | some v₁ => match isOffset t with
    | some (t, k₂) => -- v₁ =?= t+k₂
      if v₁ ≥ k₂ then isDefEq (mkNatLit $ v₁ - k₂) t else pure LBool.false
    | none => match evalNat t with
      | some v₂ => pure (v₁ == v₂).toLBool -- v₁ =?= v₂
      | none    => pure LBool.undef
  | none    => pure LBool.undef

end Meta
end Lean
