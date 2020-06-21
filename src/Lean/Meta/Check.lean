/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.InferType

/-
This is not the Kernel type checker, but an auxiliary method for checking
whether terms produced by tactics and `isDefEq` are type correct.
-/

namespace Lean
namespace Meta

private def ensureType (e : Expr) : MetaM Unit := do
_ ← getLevel e; pure ()

@[specialize] private def checkLambdaLet
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
lambdaTelescope e $ fun xs b => do
  xs.forM $ fun x => do {
    xDecl ← getFVarLocalDecl x;
    match xDecl with
    | LocalDecl.cdecl _ _ _ t _ => do
      ensureType t;
      check t
    | LocalDecl.ldecl _ _ _ t v => do
      ensureType t;
      check t;
      vType ← inferType v;
      unlessM (isExprDefEqAux t vType) $ throwEx $ Exception.letTypeMismatch x.fvarId!;
      check v
  };
  check b

@[specialize] private def checkForall
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
forallTelescope e $ fun xs b => do
  xs.forM $ fun x => do {
    xDecl ← getFVarLocalDecl x;
    ensureType xDecl.type;
    check xDecl.type
  };
  ensureType b;
  check b

private def checkConstant (c : Name) (lvls : List Level) : MetaM Unit := do
env ← getEnv;
match env.find? c with
| none       => throwEx $ Exception.unknownConst c
| some cinfo => unless (lvls.length == cinfo.lparams.length) $ throwEx $ Exception.incorrectNumOfLevels c lvls

@[specialize] private def checkApp
    (check   : Expr → MetaM Unit)
    (f a : Expr) : MetaM Unit := do
check f;
check a;
fType ← inferType f;
fType ← whnf fType;
match fType with
| Expr.forallE _ d _ _ => do
  aType ← inferType a;
  unlessM (isExprDefEqAux d aType) $ throwEx $ Exception.appTypeMismatch f a
| _ => throwEx $ Exception.functionExpected f a

private partial def checkAux : Expr → MetaM Unit
| e@(Expr.forallE _ _ _ _) => checkForall checkAux e
| e@(Expr.lam _ _ _ _)     => checkLambdaLet checkAux e
| e@(Expr.letE _ _ _ _ _)  => checkLambdaLet checkAux e
| Expr.const c lvls _      => checkConstant c lvls
| Expr.app f a _           => checkApp checkAux f a
| Expr.mdata _ e _         => checkAux e
| Expr.proj _ _ e _        => checkAux e
| _                        => pure ()

def check (e : Expr) : MetaM Unit :=
traceCtx `Meta.check $
  withTransparency TransparencyMode.all $ checkAux e

def isTypeCorrect (e : Expr) : MetaM Bool :=
catch
  (traceCtx `Meta.check $ do checkAux e; pure true)
  (fun ex => do
    trace! `Meta.typeError ex.toTraceMessageData;
    pure false)

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta.check;
registerTraceClass `Meta.typeError

end Meta
end Lean
