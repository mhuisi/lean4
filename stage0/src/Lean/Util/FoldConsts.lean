/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Option
import Lean.Expr
import Lean.Environment

namespace Lean
namespace Expr
namespace FoldConstsImpl

abbrev cacheSize : USize := 8192

structure State :=
(visitedTerms  : Array Expr)  -- Remark: cache based on pointer address. Our "unsafe" implementation relies on the fact that `()` is not a valid Expr
(visitedConsts : NameHashSet) -- cache based on structural equality

abbrev FoldM := StateM State

@[inline] unsafe def visited (e : Expr) (size : USize) : FoldM Bool := do
s ← get;
let h := ptrAddrUnsafe e;
let i := h % size;
let k := s.visitedTerms.uget i lcProof;
if ptrAddrUnsafe k == h then pure true
else do
  modify $ fun s => { s with visitedTerms := s.visitedTerms.uset i e lcProof };
  pure false

@[specialize] unsafe partial def fold {α : Type} (f : Name → α → α) (size : USize) : Expr → α → FoldM α
| e, acc => condM (liftM $ visited e size) (pure acc) $
  match e with
  | Expr.forallE _ d b _   => do acc ← fold d acc; fold b acc
  | Expr.lam _ d b _       => do acc ← fold d acc; fold b acc
  | Expr.mdata _ b _       => fold b acc
  | Expr.letE _ t v b _    => do acc ← fold t acc; acc ← fold v acc; fold b acc
  | Expr.app f a _         => do acc ← fold f acc; fold a acc
  | Expr.proj _ _ b _      => fold b acc
  | Expr.const c _ _       => do
    s ← get;
    if s.visitedConsts.contains c then pure acc
    else do
      modify $ fun s => { s with visitedConsts := s.visitedConsts.insert c };
      pure $ f c acc
  | _                      => pure acc

unsafe def initCache : State :=
{ visitedTerms  := mkArray cacheSize.toNat (cast lcProof ()),
  visitedConsts := {} }

@[inline] unsafe def foldUnsafe {α : Type} (e : Expr) (init : α) (f : Name → α → α) : α :=
(fold f cacheSize e init).run' initCache

end FoldConstsImpl

/-- Apply `f` to every constant occurring in `e` once. -/
@[implementedBy FoldConstsImpl.foldUnsafe]
constant foldConsts {α : Type} (e : Expr) (init : α) (f : Name → α → α) : α := init

end Expr

def getMaxHeight (env : Environment) (e : Expr) : UInt32 :=
e.foldConsts 0 $ fun constName max =>
  match env.find? constName with
  | ConstantInfo.defnInfo val =>
    match val.hints with
    | ReducibilityHints.regular h => if h > max then h else max
    | _                           => max
  | _ => max

end Lean
