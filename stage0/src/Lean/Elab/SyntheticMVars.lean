/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Elab.Term
import Lean.Elab.Tactic.Basic

namespace Lean
namespace Elab
namespace Term

open Tactic (TacticM evalTactic getUnsolvedGoals)

def liftTacticElabM {α} (ref : Syntax) (mvarId : MVarId) (x : TacticM α) : TermElabM α :=
withMVarContext mvarId $ fun ctx s =>
  let savedSyntheticMVars := s.syntheticMVars;
  match x { ctx with ref := ref, main := mvarId } { s with goals := [mvarId], syntheticMVars := [] } with
  | EStateM.Result.error ex newS => EStateM.Result.error (Term.Exception.ex ex) { newS.toTermState with syntheticMVars := savedSyntheticMVars }
  | EStateM.Result.ok a newS     => EStateM.Result.ok a { newS.toTermState with syntheticMVars := savedSyntheticMVars }

def ensureAssignmentHasNoMVars (ref : Syntax) (mvarId : MVarId) : TermElabM Unit := do
val ← instantiateMVars ref (mkMVar mvarId);
when val.hasExprMVar $ throwError ref ("tactic failed, result still contain metavariables" ++ indentExpr val)

def runTactic (ref : Syntax) (mvarId : MVarId) (tacticCode : Syntax) : TermElabM Unit := do
modify $ fun s => { s with mctx := s.mctx.instantiateMVarDeclMVars mvarId };
remainingGoals ← liftTacticElabM ref mvarId $ do { evalTactic tacticCode; getUnsolvedGoals };
let tailRef := ref.getTailWithPos.getD ref;
unless remainingGoals.isEmpty (reportUnsolvedGoals tailRef remainingGoals);
ensureAssignmentHasNoMVars tailRef mvarId

/-- Auxiliary function used to implement `synthesizeSyntheticMVars`. -/
private def resumeElabTerm (stx : Syntax) (expectedType? : Option Expr) (errToSorry := true) : TermElabM Expr :=
-- Remark: if `ctx.errToSorry` is already false, then we don't enable it. Recall tactics disable `errToSorry`
adaptReader (fun (ctx : Context) => { ctx with errToSorry := ctx.errToSorry && errToSorry }) $
  elabTerm stx expectedType? false

/--
  Try to elaborate `stx` that was postponed by an elaboration method using `Expection.postpone`.
  It returns `true` if it succeeded, and `false` otherwise.
  It is used to implement `synthesizeSyntheticMVars`. -/
private def resumePostponed (macroStack : MacroStack) (stx : Syntax) (mvarId : MVarId) (postponeOnError : Bool) : TermElabM Bool := do
withMVarContext mvarId $ do
  s ← get;
  catch
    (adaptReader (fun (ctx : Context) => { ctx with macroStack := macroStack }) $ do
      mvarDecl     ← getMVarDecl mvarId;
      expectedType ← instantiateMVars stx mvarDecl.type;
      result       ← resumeElabTerm stx expectedType (!postponeOnError);
      /- We must ensure `result` has the expected type because it is the one expected by the method that postponed stx.
         That is, the method does not have an opportunity to check whether `result` has the expected type or not. -/
      result ← ensureHasType stx expectedType result;
      assignExprMVar mvarId result;
      pure true)
    (fun ex => match ex with
      | Exception.postpone                            => do set s; pure false
      | Exception.ex Elab.Exception.unsupportedSyntax => unreachable!
      | Exception.ex (Elab.Exception.error msg)       =>
        if postponeOnError then do
          set s; pure false
        else do
          logMessage msg; pure true)

/--
  Similar to `synthesizeInstMVarCore`, but makes sure that `instMVar` local context and instances
  are used. It also logs any error message produced. -/
private def synthesizePendingInstMVar (ref : Syntax) (instMVar : MVarId) : TermElabM Bool := do
withMVarContext instMVar $ catch
  (synthesizeInstMVarCore ref instMVar)
  (fun ex => match ex with
    | Exception.ex (Elab.Exception.error errMsg) => do logMessage errMsg; pure true
    | _ => unreachable!)

/--
  Similar to `synthesizePendingInstMVar`, but generates type mismatch error message. -/
private def synthesizePendingCoeInstMVar (ref : Syntax) (instMVar : MVarId) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Bool := do
withMVarContext instMVar $ catch
  (synthesizeInstMVarCore ref instMVar)
  (fun ex => match ex with
    | Exception.ex (Elab.Exception.error errMsg) => throwTypeMismatchError ref expectedType eType e f? errMsg.data
    | _ => unreachable!)

/--
  Return `true` iff `mvarId` is assigned to a term whose the
  head is not a metavariable. We use this method to process `SyntheticMVarKind.withDefault`. -/
private def checkWithDefault (ref : Syntax) (mvarId : MVarId) : TermElabM Bool := do
val ← instantiateMVars ref (mkMVar mvarId);
pure $ !val.getAppFn.isMVar

/-- Try to synthesize the given pending synthetic metavariable. -/
private def synthesizeSyntheticMVar (mvarSyntheticDecl : SyntheticMVarDecl) (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool :=
match mvarSyntheticDecl.kind with
| SyntheticMVarKind.typeClass                   => synthesizePendingInstMVar mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId
| SyntheticMVarKind.coe expectedType eType e f? => synthesizePendingCoeInstMVar mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId expectedType eType e f?
-- NOTE: actual processing at `synthesizeSyntheticMVarsAux`
| SyntheticMVarKind.withDefault _               => checkWithDefault mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId
| SyntheticMVarKind.postponed macroStack        => resumePostponed macroStack mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId postponeOnError
| SyntheticMVarKind.tactic tacticCode           =>
  if runTactics then do
    runTactic mvarSyntheticDecl.ref mvarSyntheticDecl.mvarId tacticCode;
    pure true
  else
    pure false

/--
  Try to synthesize the current list of pending synthetic metavariables.
  Return `true` if at least one of them was synthesized. -/
private def synthesizeSyntheticMVarsStep (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool := do
ctx ← read;
traceAtCmdPos `Elab.resuming $ fun _ =>
  fmt "resuming synthetic metavariables, mayPostpone: " ++ fmt ctx.mayPostpone ++ ", postponeOnError: " ++ toString postponeOnError;
s ← get;
let syntheticMVars    := s.syntheticMVars;
let numSyntheticMVars := syntheticMVars.length;
-- We reset `syntheticMVars` because new synthetic metavariables may be created by `synthesizeSyntheticMVar`.
modify $ fun s => { s with syntheticMVars := [] };
-- Recall that `syntheticMVars` is a list where head is the most recent pending synthetic metavariable.
-- We use `filterRevM` instead of `filterM` to make sure we process the synthetic metavariables using the order they were created.
-- It would not be incorrect to use `filterM`.
remainingSyntheticMVars ← syntheticMVars.filterRevM $ fun mvarDecl => do {
   trace `Elab.postpone mvarDecl.ref $ fun _ => "resuming ?" ++ mvarDecl.mvarId;
   succeeded ← synthesizeSyntheticMVar mvarDecl postponeOnError runTactics;
   trace `Elab.postpone mvarDecl.ref $ fun _ => if succeeded then fmt "succeeded" else fmt "not ready yet";
   pure $ !succeeded
};
-- Merge new synthetic metavariables with `remainingSyntheticMVars`, i.e., metavariables that still couldn't be synthesized
modify $ fun s => { s with syntheticMVars := s.syntheticMVars ++ remainingSyntheticMVars };
pure $ numSyntheticMVars != remainingSyntheticMVars.length

/-- Apply default value to any pending synthetic metavariable of kind `SyntheticMVarKind.withDefault` -/
private def synthesizeUsingDefault : TermElabM Bool := do
s ← get;
let len := s.syntheticMVars.length;
newSyntheticMVars ← s.syntheticMVars.filterM $ fun mvarDecl =>
  match mvarDecl.kind with
  | SyntheticMVarKind.withDefault defaultVal => withMVarContext mvarDecl.mvarId $ do
      val ← instantiateMVars mvarDecl.ref (mkMVar mvarDecl.mvarId);
      when val.getAppFn.isMVar $
        unlessM (isDefEq mvarDecl.ref val defaultVal) $
          throwError mvarDecl.ref "failed to assign default value to metavariable"; -- TODO: better error message
      pure false
  | _ => pure true;
modify $ fun s => { s with syntheticMVars := newSyntheticMVars };
pure $ newSyntheticMVars.length != len

/-- Report an error for each synthetic metavariable that could not be resolved. -/
private def reportStuckSyntheticMVars : TermElabM Unit := do
s ← get;
s.syntheticMVars.forM $ fun mvarSyntheticDecl =>
  match mvarSyntheticDecl.kind with
  | SyntheticMVarKind.typeClass =>
    withMVarContext mvarSyntheticDecl.mvarId $ do
      mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId;
      logError mvarSyntheticDecl.ref $
        "failed to create type class instance for " ++ indentExpr mvarDecl.type
  | SyntheticMVarKind.coe expectedType eType e f? =>
    withMVarContext mvarSyntheticDecl.mvarId $ do
      mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId;
      throwTypeMismatchError mvarSyntheticDecl.ref expectedType eType e f? (some ("failed to create type class instance for " ++ indentExpr mvarDecl.type))
  | _ => unreachable! -- TODO handle other cases.

private def getSomeSynthethicMVarsRef : TermElabM Syntax := do
s ← get;
match s.syntheticMVars.find? $ fun (mvarDecl : SyntheticMVarDecl) => !mvarDecl.ref.getPos.isNone with
| some mvarDecl => pure mvarDecl.ref
| none          => pure Syntax.missing

/--
  Main loop for `synthesizeSyntheticMVars.
  It keeps executing `synthesizeSyntheticMVarsStep` while progress is being made.
  If `mayPostpone == false`, then it applies default values to `SyntheticMVarKind.withDefault`
  metavariables that are still unresolved, and then tries to resolve metavariables
  with `mayPostpone == false`. That is, we force them to produce error messages and/or commit to
  a "best option". If, after that, we still haven't made progress, we report "stuck" errors. -/
private partial def synthesizeSyntheticMVarsAux (mayPostpone := true) : Unit → TermElabM Unit
| _ => do
  let try (x : TermElabM Bool) (k : TermElabM Unit) : TermElabM Unit := condM x (synthesizeSyntheticMVarsAux ()) k;
  ref ← getSomeSynthethicMVarsRef;
  withIncRecDepth ref $ do
    s ← get;
    unless s.syntheticMVars.isEmpty $ do
      try (synthesizeSyntheticMVarsStep false false) $
      unless mayPostpone $ do
        /- Resume pending metavariables with "elaboration postponement" disabled.
           We postpone elaboration errors in this step by setting `postponeOnError := true`.
           Example:
           ```
           #check let x := ⟨1, 2⟩; Prod.fst x
           ```
           The term `⟨1, 2⟩` can't be elaborated because the expected type is not know.
           The `x` at `Prod.fst x` is not elaborated because the type of `x` is not known.
           When we execute the following step with "elaboration postponement" disabled,
           the elaborator fails at `⟨1, 2⟩` and postpones it, and succeeds at `x` and learns
           that its type must be of the form `Prod ?α ?β`.

           Recall that we postponed `x` at `Prod.fst x` because its type it is not known.
           We the type of `x` may learn later its type and it may contain implicit and/or auto arguments.
           By disabling postponement, we are essentially giving up the opportunity of learning `x`s type
           and assume it does not have implict and/or auto arguments. -/
        try (withoutPostponing (synthesizeSyntheticMVarsStep true  false)) $
        try synthesizeUsingDefault $
        try (withoutPostponing (synthesizeSyntheticMVarsStep false false)) $
        try (synthesizeSyntheticMVarsStep false true) $
        reportStuckSyntheticMVars

/--
  Try to process pending synthetic metavariables. If `mayPostpone == false`,
  then `syntheticMVars` is `[]` after executing this method.  -/
def synthesizeSyntheticMVars (mayPostpone := true) : TermElabM Unit :=
synthesizeSyntheticMVarsAux mayPostpone ()

/-- Elaborate `stx`, and make sure all pending synthetic metavariables created while elaborating `stx` are solved. -/
def elabTermAndSynthesize (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
s ← get;
let syntheticMVars := s.syntheticMVars;
modify $ fun s => { s with syntheticMVars := [] };
finally
  (do
     v ← elabTerm stx expectedType?;
     synthesizeSyntheticMVars false;
     instantiateMVars stx v)
  (modify $ fun s => { s with syntheticMVars := s.syntheticMVars ++ syntheticMVars })

end Term
end Elab
end Lean
