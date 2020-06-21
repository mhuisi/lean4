/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The Reader monad transformer for passing immutable State.
-/

prelude
import Init.Control.Lift
import Init.Control.Id
import Init.Control.Alternative
import Init.Control.Except
universes u v w

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
ρ → m α

@[inline] def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
x r

@[reducible] def Reader (ρ : Type u) := ReaderT ρ id

namespace ReaderT
section
variables {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def read : ReaderT ρ m ρ :=
pure

@[inline] protected def pure (a : α) : ReaderT ρ m α :=
fun r => pure a

@[inline] protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
fun r => do a ← x r; f a r

@[inline] protected def map (f : α → β) (x : ReaderT ρ m α) : ReaderT ρ m β :=
fun r => f <$> x r

instance : Monad (ReaderT ρ m) :=
{ pure := @ReaderT.pure _ _ _, bind := @ReaderT.bind _ _ _, map := @ReaderT.map _ _ _ }

@[inline] protected def lift (a : m α) : ReaderT ρ m α :=
fun r => a

instance (m) [Monad m] : HasMonadLift m (ReaderT ρ m) :=
⟨@ReaderT.lift ρ m _⟩

instance (ρ m m') [Monad m] [Monad m'] : MonadFunctor m m' (ReaderT ρ m) (ReaderT ρ m') :=
⟨fun _ f x r => f (x r)⟩

@[inline] protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
fun x r => x (f r)

@[inline] protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : ReaderT ρ m α) : ReaderT ρ m α :=
fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : ReaderT ρ m α :=
fun s => failure

instance [Alternative m] : Alternative (ReaderT ρ m) :=
{ ReaderT.Monad with
  failure := @ReaderT.failure _ _ _ _,
  orelse  := @ReaderT.orelse _ _ _ _ }


instance (ε) [Monad m] [MonadExcept ε m] : MonadExcept ε (ReaderT ρ m) :=
{ throw := fun α => ReaderT.lift ∘ throw,
  catch := fun α x c r => catch (x r) (fun e => (c e) r) }
end
end ReaderT

/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this Function cannot be lifted using `monadLift`.
    Instead, the `MonadReaderAdapter` class provides the more general `adaptReader` Function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReader (ρ : outParam (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α) → n α)
    ```
    -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
(read : m ρ)

export MonadReader (read)

instance monadReaderTrans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w}
  [MonadReader ρ m] [HasMonadLift m n] : MonadReader ρ n :=
⟨monadLift (MonadReader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReader ρ (ReaderT ρ m) :=
⟨ReaderT.read⟩


/-- Adapt a Monad stack, changing the Type of its top-most environment.

    This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify), but does not use lenses (why would it), and is derived automatically for any transformer implementing `MonadFunctor`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReaderFunctor (ρ ρ' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α → ReaderT ρ' m α) → n α → n' α)
    ```
    -/
class MonadReaderAdapter (ρ ρ' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptReader {α : Type u} : (ρ' → ρ) → m α → m' α)
export MonadReaderAdapter (adaptReader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type v}

instance monadReaderAdapterTrans {n n' : Type u → Type v} [MonadReaderAdapter ρ ρ' m m'] [MonadFunctor m m' n n'] : MonadReaderAdapter ρ ρ' n n' :=
⟨fun α f => monadMap (fun α => (adaptReader f : m α → m' α))⟩

instance [Monad m] : MonadReaderAdapter ρ ρ' (ReaderT ρ m) (ReaderT ρ' m) :=
⟨fun α => ReaderT.adapt⟩
end

instance (ρ : Type u) (m out) [MonadRun out m] : MonadRun (fun α => ρ → out α) (ReaderT ρ m) :=
⟨fun α x => run ∘ x⟩

class MonadReaderRunner (ρ : Type u) (m m' : Type u → Type u) :=
(runReader {α : Type u} : m α → ρ → m' α)
export MonadReaderRunner (runReader)

section
variables {ρ ρ' : Type u} {m m' : Type u → Type u}

instance monadReaderRunnerTrans {n n' : Type u → Type u} [MonadReaderRunner ρ m m'] [MonadFunctor m m' n n'] : MonadReaderRunner ρ n n' :=
⟨fun α x r => monadMap (fun (α) (y : m α) => (runReader y r : m' α)) x⟩

instance ReaderT.MonadStateRunner [Monad m] : MonadReaderRunner ρ (ReaderT ρ m) m :=
⟨fun α x r => x r⟩
end
