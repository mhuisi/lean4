/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Control.Monad
import Init.Control.Alternative
import Init.Coe
open Decidable

universes u v

namespace Option

def toMonad {m : Type → Type} [Monad m] [Alternative m] {A} : Option A → m A
| none => failure
| some a   => pure a

@[macroInline] def getD {α : Type u} : Option α → α → α
| some x, _ => x
| none,   e => e

@[inline] def toBool {α : Type u} : Option α → Bool
| some _ => true
| none   => false

@[inline] def isSome {α : Type u} : Option α → Bool
| some _ => true
| none   => false

@[inline] def isNone {α : Type u} : Option α → Bool
| some _ => false
| none   => true

@[inline] protected def bind {α : Type u} {β : Type v} : Option α → (α → Option β) → Option β
| none,   b => none
| some a, b => b a

@[inline] protected def map {α β} (f : α → β) (o : Option α) : Option β :=
Option.bind o (some ∘ f)

theorem mapId {α} : (Option.map id : Option α → Option α) = id :=
funext (fun o => match o with | none => rfl | some x => rfl)

instance : Monad Option :=
{pure := @some, bind := @Option.bind, map := @Option.map}

@[inline] protected def filter {α} (p : α → Bool) : Option α → Option α
| some a => if p a then some a else none
| none   => none

@[inline] protected def all {α} (p : α → Bool) : Option α → Bool
| some a => p a
| none   => true

@[inline] protected def any {α} (p : α → Bool) : Option α → Bool
| some a => p a
| none   => false

@[macroInline] protected def orelse {α : Type u} : Option α → Option α → Option α
| some a, _ => some a
| none,   b => b

/- Remark: when using the polymorphic notation `a <|> b` is not a `[macroInline]`.
   Thus, `a <|> b` will make `Option.orelse` to behave like it was marked as `[inline]`. -/
instance : Alternative Option :=
{ Option.Monad with
  failure := @none,
  orelse  := @Option.orelse }

@[inline] protected def lt {α : Type u} (r : α → α → Prop) : Option α → Option α → Prop
| none, some x     => True
| some x,   some y => r x y
| _, _             => False

instance decidableRelLt {α : Type u} (r : α → α → Prop) [s : DecidableRel r] : DecidableRel (Option.lt r)
| none,   some y => isTrue  trivial
| some x, some y => s x y
| some x, none   => isFalse notFalse
| none,   none   => isFalse notFalse

end Option

instance (α : Type u) : Inhabited (Option α) :=
⟨none⟩

instance {α : Type u} [DecidableEq α] : DecidableEq (Option α) :=
fun a b => match a, b with
 | none,      none      => isTrue rfl
 | none,      (some v₂) => isFalse (fun h => Option.noConfusion h)
 | (some v₁), none      => isFalse (fun h => Option.noConfusion h)
 | (some v₁), (some v₂) =>
   match decEq v₁ v₂ with
   | (isTrue e)  => isTrue (congrArg (@some α) e)
   | (isFalse n) => isFalse (fun h => Option.noConfusion h (fun e => absurd e n))

instance {α : Type u} [HasBeq α] : HasBeq (Option α) :=
⟨fun a b => match a, b with
 | none,      none      => true
 | none,      (some v₂) => false
 | (some v₁), none      => false
 | (some v₁), (some v₂) => v₁ == v₂⟩

instance {α : Type u} [HasLess α] : HasLess (Option α) := ⟨Option.lt HasLess.Less⟩
