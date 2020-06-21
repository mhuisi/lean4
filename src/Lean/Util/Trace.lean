/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Lean.Message
universe u

namespace Lean

class MonadTracer (m : Type → Type u) :=
(traceCtx {α} : Name → m α → m α)
(trace  : Name → (Unit → MessageData) → m PUnit)
(traceM : Name → m MessageData → m PUnit)

class MonadTracerAdapter (m : Type → Type) :=
(isTracingEnabledFor : Name → m Bool)
(addContext          : MessageData → m MessageData)
(enableTracing       : Bool → m Bool)
(getTraces           : m (PersistentArray MessageData))
(modifyTraces        : (PersistentArray MessageData → PersistentArray MessageData) → m Unit)

private def checkTraceOptionAux (opts : Options) : Name → Bool
| n@(Name.str p _ _) => opts.getBool n || (!opts.contains n && checkTraceOptionAux p)
| _                  => false

def checkTraceOption (opts : Options) (cls : Name) : Bool :=
if opts.isEmpty then false
else checkTraceOptionAux opts (`trace ++ cls)

namespace MonadTracerAdapter

section
variables {m : Type → Type}
variables [Monad m] [MonadTracerAdapter m]
variables {α : Type}

private def addNode (oldTraces : PersistentArray MessageData) (cls : Name) : m Unit :=
modifyTraces $ fun traces =>
  let d := MessageData.tagged cls (MessageData.node traces.toArray);
  oldTraces.push d

private def getResetTraces : m (PersistentArray MessageData) := do
oldTraces ← getTraces;
modifyTraces $ fun _ => {};
pure oldTraces

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
msg ← addContext msg;
modifyTraces $ fun traces => traces.push (MessageData.tagged cls msg)

@[inline] protected def trace (cls : Name) (msg : Unit → MessageData) : m Unit :=
whenM (isTracingEnabledFor cls) (addTrace cls (msg ()))

@[inline] protected def traceM (cls : Name) (mkMsg : m MessageData) : m Unit :=
whenM (isTracingEnabledFor cls) (do msg ← mkMsg; addTrace cls msg)

@[inline] def traceCtx (cls : Name) (ctx : m α) : m α := do
b ← isTracingEnabledFor cls;
if !b then do old ← enableTracing false; a ← ctx; _ ← enableTracing old; pure a
else do
  oldCurrTraces ← getResetTraces;
  a ← ctx;
  addNode oldCurrTraces cls;
  pure a

end

section
variables {ε : Type} {m : Type → Type}
variables [MonadExcept ε m] [Monad m] [MonadTracerAdapter m]
variables {α : Type}

/- Version of `traceCtx` with exception handling support. -/
@[inline] protected def traceCtxExcept (cls : Name) (ctx : m α) : m α := do
b ← isTracingEnabledFor cls;
if !b then do
  old ← enableTracing false;
  catch
    (do a ← ctx; _ ← enableTracing old; pure a)
    (fun e => do _ ← enableTracing old; throw e)
else do
  oldCurrTraces ← getResetTraces;
  catch
    (do a ← ctx; addNode oldCurrTraces cls; pure a)
    (fun e => do addNode oldCurrTraces cls; throw e)
end

end MonadTracerAdapter

instance monadTracerAdapter {m : Type → Type} [Monad m] [MonadTracerAdapter m] : MonadTracer m :=
{ traceCtx := @MonadTracerAdapter.traceCtx _ _ _,
  trace    := @MonadTracerAdapter.trace _ _ _,
  traceM   := @MonadTracerAdapter.traceM _ _ _ }

instance monadTracerAdapterExcept {ε : Type} {m : Type → Type} [Monad m] [MonadExcept ε m] [MonadTracerAdapter m] : MonadTracer m :=
{ traceCtx := @MonadTracerAdapter.traceCtxExcept _ _ _ _ _,
  trace    := @MonadTracerAdapter.trace _ _ _,
  traceM   := @MonadTracerAdapter.traceM _ _ _ }

instance liftMonadTracerAdapter {m n : Type → Type} [MonadTracerAdapter n] [HasMonadLift n m] : MonadTracerAdapter m :=
{ isTracingEnabledFor := fun cls => liftM (MonadTracerAdapter.isTracingEnabledFor cls : n _),
  addContext := fun msg => liftM (MonadTracerAdapter.addContext msg : n _),
  enableTracing := fun b => liftM (MonadTracerAdapter.enableTracing b : n _),
  getTraces := liftM (MonadTracerAdapter.getTraces : n _),
  modifyTraces := fun f => liftM (MonadTracerAdapter.modifyTraces f : n _) }

structure TraceState :=
(enabled : Bool := true)
(traces  : PersistentArray MessageData := {})

namespace TraceState

instance : Inhabited TraceState := ⟨{}⟩

private def toFormat (traces : PersistentArray MessageData) (sep : Format) : Format :=
traces.size.fold
  (fun i r =>
    let curr := format $ traces.get! i;
    if i > 0 then r ++ sep ++ curr else r ++ curr)
  Format.nil

instance : HasFormat TraceState := ⟨fun s => toFormat s.traces Format.line⟩

instance : HasToString TraceState := ⟨toString ∘ fmt⟩

end TraceState

class SimpleMonadTracerAdapter (m : Type → Type) :=
(getOptions        : m Options)
(modifyTraceState  : (TraceState → TraceState) → m Unit)
(getTraceState     : m TraceState)
(addContext        : MessageData → m MessageData)

namespace SimpleMonadTracerAdapter
variables {m : Type → Type} [Monad m] [SimpleMonadTracerAdapter m]

private def checkTraceOptionM (cls : Name) : m Bool := do
opts ← getOptions;
pure $ checkTraceOption opts cls

@[inline] def isTracingEnabledFor (cls : Name) : m Bool := do
s ← getTraceState;
if !s.enabled then pure false
else checkTraceOptionM cls

@[inline] def enableTracing (b : Bool) : m Bool := do
s ← getTraceState;
let oldEnabled := s.enabled;
modifyTraceState $ fun s => { s with enabled := b };
pure oldEnabled

@[inline] def getTraces : m (PersistentArray MessageData) := do
s ← getTraceState; pure s.traces

@[inline] def modifyTraces (f : PersistentArray MessageData → PersistentArray MessageData) : m Unit :=
modifyTraceState $ fun s => { s with traces := f s.traces }

@[inline] def setTrace (f : PersistentArray MessageData → PersistentArray MessageData) : m Unit :=
modifyTraceState $ fun s => { s with traces := f s.traces }

@[inline] def setTraceState (s : TraceState) : m Unit :=
modifyTraceState $ fun _ => s

end SimpleMonadTracerAdapter

instance simpleMonadTracerAdapter {m : Type → Type} [SimpleMonadTracerAdapter m] [Monad m] : MonadTracerAdapter m :=
{ isTracingEnabledFor := @SimpleMonadTracerAdapter.isTracingEnabledFor _ _ _,
  enableTracing       := @SimpleMonadTracerAdapter.enableTracing _ _ _,
  getTraces           := @SimpleMonadTracerAdapter.getTraces _ _ _,
  addContext          := @SimpleMonadTracerAdapter.addContext _ _,
  modifyTraces        := @SimpleMonadTracerAdapter.modifyTraces _ _ _ }

export MonadTracer (traceCtx trace traceM)

/-
Recipe for adding tracing support for a monad `M`.

1- Define the instance `SimpleMonadTracerAdapter M` by showing how to retrieve `Options` and
   get/modify `TraceState` object.

2- The `Options` control whether tracing commands are ignored or not.

3- The macro `trace! <cls> <msg>` adds the trace message `<msg>` if `<cls>` is activate and tracing is enabled.

4- We activate the tracing class `<cls>` by setting option `trace.<cls>` to true. If a prefix `p` of `trace.<cls>` is
   set to true, and there isn't a longer prefix `p'` set to false, then `<cls>` is also considered active.

5- `traceCtx <cls> <action>` groups all messages generated by `<action>` into a single `MessageData.node`.
    If `<cls> is not activate, then (all) tracing is disabled while executing `<action>`. This feature is
    useful for the following scenario:
     a) We have a tactic called `mysimp` which uses trace class `mysimp`.
     b) `mysimp invokes the unifier module which uses trace class `unify`.
     c) In the beginning of `mysimp`, we use `traceCtx`.
    In this scenario, by not enabling `mysimp` we also disable the `unify` trace messages produced
    by executing `mysimp`.
-/

def registerTraceClass (traceClassName : Name) : IO Unit :=
registerOption (`trace ++ traceClassName) { group := "trace", defValue := false, descr := "enable/disable tracing for the given module and submodules" }

end Lean
