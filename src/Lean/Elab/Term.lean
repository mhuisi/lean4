/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Sorry
import Lean.Structure
import Lean.Meta.ExprDefEq
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Util
import Lean.Hygiene
import Lean.Util.RecDepth
import Lean.Elab.Log
import Lean.Elab.Alias
import Lean.Elab.ResolveName
import Lean.Elab.Level

namespace Lean
namespace Elab
namespace Term

structure Context extends Meta.Context :=
(fileName        : String)
(fileMap         : FileMap)
(cmdPos          : String.Pos)
(currNamespace   : Name)
(declName?       : Option Name     := none)
(levelNames      : List Name       := [])
(openDecls       : List OpenDecl   := [])
(macroStack      : MacroStack      := [])
(currMacroScope  : MacroScope      := firstFrontendMacroScope)
/- When `mayPostpone == true`, an elaboration function may interrupt its execution by throwing `Exception.postpone`.
   The function `elabTerm` catches this exception and creates fresh synthetic metavariable `?m`, stores `?m` in
   the list of pending synthetic metavariables, and returns `?m`. -/
(mayPostpone     : Bool            := true)
/- When `errToSorry` is set to true, the method `elabTerm` catches
   exceptions and converts them into synthetic `sorry`s.
   The implementation of choice nodes and overloaded symbols rely on the fact
   that when `errToSorry` is set to false for an elaboration function `F`, then
   `errToSorry` remains `false` for all elaboration functions invoked by `F`.
   That is, it is safe to transition `errToSorry` from `true` to `false`, but
   we must not set `errToSorry` to `true` when it is currently set to `false`. -/
(errToSorry      : Bool            := true)
/- If `macroStackAtErr == true`, we include it in error messages. -/
(macroStackAtErr : Bool            := true)

/-- We use synthetic metavariables as placeholders for pending elaboration steps. -/
inductive SyntheticMVarKind
-- typeclass instance search
| typeClass
-- Similar to typeClass, but error messages are different,
-- we use "type mismatch" or "application type mismatch" (when `f?` is some) instead of "failed to synthesize"
| coe (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr)
-- tactic block execution
| tactic (tacticCode : Syntax)
-- `elabTerm` call that threw `Exception.postpone` (input is stored at `SyntheticMVarDecl.ref`)
| postponed (macroStack : MacroStack)
-- type defaulting (currently: defaulting numeric literals to `Nat`)
| withDefault (defaultVal : Expr)

structure SyntheticMVarDecl :=
(mvarId : MVarId) (ref : Syntax) (kind : SyntheticMVarKind)

structure State extends Meta.State :=
(syntheticMVars  : List SyntheticMVarDecl := [])
(messages        : MessageLog := {})
(instImplicitIdx : Nat := 1)
(anonymousIdx    : Nat := 1)
(nextMacroScope  : Nat := firstFrontendMacroScope + 1)

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _ }⟩

/-
  The Term elaborator monad has a special kind of exception `Exception.postpone` which is used by
  an elaboration function to notify the main driver that it should be tried later.

  Remark: `Exception.postpone` is used only when `mayPostpone == true` in the `Context`. -/
inductive Exception
| ex       : Elab.Exception → Exception
| postpone : Exception

instance Exception.inhabited : Inhabited Exception := ⟨Exception.postpone⟩
instance Exception.hasToString : HasToString Exception :=
⟨fun ex => match ex with | Exception.postpone => "postponed" | Exception.ex ex => toString ex⟩

/-
  Term elaborator Monad. In principle, we could track statically which methods
  may postpone or not by having adding a Boolean parameter `mayPostpone` to
  `TermElabM`. This would be useful to ensure that `Exception.postpone` does not leak
  to `CommandElabM`, but we abandoned this design because it adds unnecessary complexity. -/
abbrev TermElabM := ReaderT Context (EStateM Exception State)
abbrev TermElab  := Syntax → Option Expr → TermElabM Expr

instance TermElabM.inhabited {α} : Inhabited (TermElabM α) :=
⟨throw $ Exception.postpone⟩

abbrev TermElabResult := EStateM.Result Message State Expr
instance TermElabResult.inhabited : Inhabited TermElabResult := ⟨EStateM.Result.ok (arbitrary _) (arbitrary _)⟩

/--
  Execute `x`, save resulting expression and new state.
  If `x` fails, then it also stores exception and new state.
  Remark: we do not capture `Exception.postpone`. -/
@[inline] def observing (x : TermElabM Expr) : TermElabM TermElabResult :=
fun ctx s =>
  match x ctx s with
  | EStateM.Result.error (Exception.ex (Elab.Exception.error errMsg)) newS => EStateM.Result.ok (EStateM.Result.error errMsg newS) s
  | EStateM.Result.error Exception.postpone _                              => EStateM.Result.error Exception.postpone s
  | EStateM.Result.error ex newS                                           => EStateM.Result.error ex newS
  | EStateM.Result.ok e newS                                               => EStateM.Result.ok (EStateM.Result.ok e newS) s

/--
  Apply the result/exception and state captured with `observing`.
  We use this method to implement overloaded notation and symbols. -/
def applyResult (result : TermElabResult) : TermElabM Expr :=
match result with
| EStateM.Result.ok e s         => do set s; pure e
| EStateM.Result.error errMsg s => do set s; throw (Exception.ex (Elab.Exception.error errMsg))

def getEnv : TermElabM Environment := do s ← get; pure s.env
def getMCtx : TermElabM MetavarContext := do s ← get; pure s.mctx
def getLCtx : TermElabM LocalContext := do ctx ← read; pure ctx.lctx
def getLocalInsts : TermElabM LocalInstances := do ctx ← read; pure ctx.localInstances
def getOptions : TermElabM Options := do ctx ← read; pure ctx.config.opts
def setEnv (env : Environment) : TermElabM Unit := modify $ fun s => { s with env := env }
def setMCtx (mctx : MetavarContext) : TermElabM Unit := modify $ fun s => { s with mctx := mctx }

def addContext (msg : MessageData) : TermElabM MessageData := do
env ← getEnv; mctx ← getMCtx; lctx ← getLCtx; opts ← getOptions;
pure (MessageData.withContext { env := env, mctx := mctx, lctx := lctx, opts := opts } msg)

instance monadLog : MonadLog TermElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext,
  logMessage  := fun msg => modify $ fun s => { s with messages := s.messages.add msg } }

/--
  Throws an error with the given `msgData` and extracting position information from `ref`.
  If `ref` does not contain position information, then use `cmdPos` -/
def throwError {α} (ref : Syntax) (msgData : MessageData) : TermElabM α := do
ctx ← read;
let ref     := getBetterRef ref ctx.macroStack;
let msgData := if ctx.macroStackAtErr then addMacroStack msgData ctx.macroStack else msgData;
msg ← mkMessage msgData MessageSeverity.error ref;
throw (Exception.ex (Elab.Exception.error msg))

def throwUnsupportedSyntax {α} : TermElabM α :=
throw (Exception.ex Elab.Exception.unsupportedSyntax)

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : TermElabM α) : TermElabM α := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throwError ref maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { ctx with currRecDepth := ctx.currRecDepth + 1 }) x

protected def getCurrMacroScope : TermElabM MacroScope := do ctx ← read; pure ctx.currMacroScope
protected def getMainModule     : TermElabM Name := do env ← getEnv; pure env.mainModule

@[inline] protected def withFreshMacroScope {α} (x : TermElabM α) : TermElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance monadQuotation : MonadQuotation TermElabM := {
  getCurrMacroScope   := Term.getCurrMacroScope,
  getMainModule       := Term.getMainModule,
  withFreshMacroScope := @Term.withFreshMacroScope
}

unsafe def mkTermElabAttribute : IO (KeyedDeclsAttribute TermElab) :=
mkElabAttribute TermElab `Lean.Elab.Term.termElabAttribute `builtinTermElab `termElab `Lean.Parser.Term `Lean.Elab.Term.TermElab "term"
@[init mkTermElabAttribute] constant termElabAttribute : KeyedDeclsAttribute TermElab := arbitrary _

/--
  Auxiliary datatatype for presenting a Lean lvalue modifier.
  We represent a unelaborated lvalue as a `Syntax` (or `Expr`) and `List LVal`.
  Example: `a.foo[i].1` is represented as the `Syntax` `a` and the list
  `[LVal.fieldName "foo", LVal.getOp i, LVal.fieldIdx 1]`.
  Recall that the notation `a[i]` is not just for accessing arrays in Lean. -/
inductive LVal
| fieldIdx  (i : Nat)
| fieldName (name : String)
| getOp     (idx : Syntax)

instance LVal.hasToString : HasToString LVal :=
⟨fun p => match p with | LVal.fieldIdx i => toString i | LVal.fieldName n => n | LVal.getOp idx => "[" ++ toString idx ++ "]"⟩

def getDeclName? : TermElabM (Option Name) := do ctx ← read; pure ctx.declName?
def getCurrNamespace : TermElabM Name := do ctx ← read; pure ctx.currNamespace
def getOpenDecls : TermElabM (List OpenDecl) := do ctx ← read; pure ctx.openDecls
def getTraceState : TermElabM TraceState := do s ← get; pure s.traceState
def setTraceState (traceState : TraceState) : TermElabM Unit := modify $ fun s => { s with traceState := traceState }
def isExprMVarAssigned (mvarId : MVarId) : TermElabM Bool := do mctx ← getMCtx; pure $ mctx.isExprAssigned mvarId
def getMVarDecl (mvarId : MVarId) : TermElabM MetavarDecl := do mctx ← getMCtx; pure $ mctx.getDecl mvarId
def assignExprMVar (mvarId : MVarId) (val : Expr) : TermElabM Unit := modify $ fun s => { s with mctx := s.mctx.assignExpr mvarId val }

def logTrace (cls : Name) (ref : Syntax) (msg : MessageData) : TermElabM Unit := do
ctx ← read;
s   ← get;
logInfo ref $
  MessageData.withContext { env := s.env, mctx := s.mctx, lctx := ctx.lctx, opts := ctx.config.opts } $
    MessageData.tagged cls msg

@[inline] def trace (cls : Name) (ref : Syntax) (msg : Unit → MessageData) : TermElabM Unit := do
opts ← getOptions;
when (checkTraceOption opts cls) $ logTrace cls ref (msg ())

def logDbgTrace (msg : MessageData) : TermElabM Unit := do
trace `Elab.debug Syntax.missing $ fun _ => msg

/-- For testing `TermElabM` methods. The #eval command will sign the error. -/
def throwErrorIfErrors : TermElabM Unit := do
s ← get;
when s.messages.hasErrors $
  throwError Syntax.missing "Error(s)"

@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TermElabM Unit :=
trace cls Syntax.missing msg

def dbgTrace {α} [HasToString α] (a : α) : TermElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

/-- Auxiliary function for `liftMetaM` -/
private def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

/-- Auxiliary function for `liftMetaM` -/
private def fromMetaException (ctx : Context) (ref : Syntax) (ex : Meta.Exception) : Exception :=
Exception.ex $ Elab.Exception.error $ mkMessageAux ctx ref ex.toMessageData MessageSeverity.error

/-- Auxiliary function for `liftMetaM` -/
private def fromMetaState (ref : Syntax) (ctx : Context) (s : State) (newS : Meta.State) (oldTraceState : TraceState) : State :=
let traces   := newS.traceState.traces;
let messages := traces.foldl (fun (messages : MessageLog) trace => messages.add (mkMessageAux ctx ref trace MessageSeverity.information)) s.messages;
{ s with
  toState  := { newS with traceState := oldTraceState },
  messages := messages }

@[inline] def liftMetaM {α} (ref : Syntax) (x : MetaM α) : TermElabM α :=
fun ctx s =>
  let oldTraceState := s.traceState;
  match x ctx.toContext { s.toState with traceState := {} } with
  | EStateM.Result.ok a newS     => EStateM.Result.ok a (fromMetaState ref ctx s newS oldTraceState)
  | EStateM.Result.error ex newS => EStateM.Result.error (fromMetaException ctx ref ex) (fromMetaState ref ctx s newS oldTraceState)

def ppGoal (ref : Syntax) (mvarId : MVarId) : TermElabM Format := liftMetaM ref $ Meta.ppGoal mvarId
def isType (ref : Syntax) (e : Expr) : TermElabM Bool := liftMetaM ref $ Meta.isType e
def isTypeFormer (ref : Syntax) (e : Expr) : TermElabM Bool := liftMetaM ref $ Meta.isTypeFormer e
def isDefEqNoConstantApprox (ref : Syntax) (t s : Expr) : TermElabM Bool := liftMetaM ref $ Meta.approxDefEq $ Meta.isDefEq t s
def isDefEq (ref : Syntax) (t s : Expr) : TermElabM Bool := liftMetaM ref $ Meta.fullApproxDefEq $ Meta.isDefEq t s
def inferType (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.inferType e
def whnf (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnf e
def whnfForall (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnfForall e
def whnfCore (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.whnfCore e
def unfoldDefinition? (ref : Syntax) (e : Expr) : TermElabM (Option Expr) := liftMetaM ref $ Meta.unfoldDefinition? e
def instantiateMVars (ref : Syntax) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.instantiateMVars e
def isClass (ref : Syntax) (t : Expr) : TermElabM (Option Name) := liftMetaM ref $ Meta.isClass t
def mkFreshLevelMVar (ref : Syntax) : TermElabM Level := liftMetaM ref $ Meta.mkFreshLevelMVar
def mkFreshExprMVar (ref : Syntax) (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
match type? with
| some type => liftMetaM ref $ Meta.mkFreshExprMVar type userName? kind
| none      => liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; type ← Meta.mkFreshExprMVar (mkSort u); Meta.mkFreshExprMVar type userName? kind
def mkFreshTypeMVar (ref : Syntax) (kind : MetavarKind := MetavarKind.natural) (userName? : Name := Name.anonymous) : TermElabM Expr :=
liftMetaM ref $ do u ← Meta.mkFreshLevelMVar; Meta.mkFreshExprMVar (mkSort u) userName? kind
def getLevel (ref : Syntax) (type : Expr) : TermElabM Level := liftMetaM ref $ Meta.getLevel type
def mkForall (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkForall xs e
def mkForallUsedOnly (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM (Expr × Nat) := liftMetaM ref $ Meta.mkForallUsedOnly xs e
def mkLambda (ref : Syntax) (xs : Array Expr) (e : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkLambda xs e
def mkLet (ref : Syntax) (x : Expr) (e : Expr) : TermElabM Expr := mkLambda ref #[x] e
def trySynthInstance (ref : Syntax) (type : Expr) : TermElabM (LOption Expr) := liftMetaM ref $ Meta.trySynthInstance type
def mkAppM (ref : Syntax) (constName : Name) (args : Array Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkAppM constName args
def mkExpectedTypeHint (ref : Syntax) (e : Expr) (expectedType : Expr) : TermElabM Expr := liftMetaM ref $ Meta.mkExpectedTypeHint e expectedType
def decLevel? (ref : Syntax) (u : Level) : TermElabM (Option Level) := liftMetaM ref $ Meta.decLevel? u

def decLevel (ref : Syntax) (u : Level) : TermElabM Level := do
u? ← decLevel? ref u;
match u? with
| some u => pure u
| none   => throwError ref ("invalid universe level, " ++ u ++ " is not greater than 0")

/- This function is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   and then decrement 1 to obtain `u`. -/
def getDecLevel (ref : Syntax) (type : Expr) : TermElabM Level := do
u ← getLevel ref type;
decLevel ref u

@[inline] def savingMCtx {α} (x : TermElabM α) : TermElabM α := do
mctx ← getMCtx;
finally x (modify $ fun s => { s with mctx := mctx })

def liftLevelM {α} (x : LevelElabM α) : TermElabM α :=
fun ctx s =>
  let lvlCtx : Level.Context := { fileName := ctx.fileName, fileMap := ctx.fileMap, cmdPos := ctx.cmdPos, levelNames := ctx.levelNames };
  match (x lvlCtx).run { ngen := s.ngen, mctx := s.mctx } with
  | EStateM.Result.ok a newS     => EStateM.Result.ok a { s with mctx := newS.mctx, ngen := newS.ngen }
  | EStateM.Result.error ex newS => EStateM.Result.error (Exception.ex ex) s

def elabLevel (stx : Syntax) : TermElabM Level :=
liftLevelM $ Level.elabLevel stx

@[inline] def withConfig {α} (f : Meta.Config → Meta.Config) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with config := f ctx.config }) x

@[inline] def withTransparency {α} (mode : Meta.TransparencyMode) (x : TermElabM α) : TermElabM α :=
withConfig (fun config => { config with transparency := mode }) x

@[inline] def withReducible {α} (x : TermElabM α) : TermElabM α :=
withTransparency Meta.TransparencyMode.reducible x

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

/-
  Add the given metavariable to the list of pending synthetic metavariables.
  The method `synthesizeSyntheticMVars` is used to process the metavariables on this list. -/
def registerSyntheticMVar (ref : Syntax) (mvarId : MVarId) (kind : SyntheticMVarKind) : TermElabM Unit :=
modify $ fun s => { s with syntheticMVars := { mvarId := mvarId, ref := ref, kind := kind } :: s.syntheticMVars }

/-
  Execute `x` without allowing it to postpone elaboration tasks.
  That is, `tryPostpone` is a noop. -/
@[inline] def withoutPostponing {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with mayPostpone := false }) x

/-- Creates syntax for `(` <ident> `:` <type> `)` -/
def mkExplicitBinder (ident : Syntax) (type : Syntax) : Syntax :=
mkNode `Lean.Parser.Term.explicitBinder #[mkAtom "(", mkNullNode #[ident], mkNullNode #[mkAtom ":", type], mkNullNode, mkAtom ")"]

/-- Convert unassigned universe level metavariables into parameters. -/
def levelMVarToParam (e : Expr) : TermElabM Expr := do
ctx ← read;
mctx ← getMCtx;
let r := mctx.levelMVarToParam (fun n => ctx.levelNames.elem n) e;
modify $ fun s => { s with mctx := r.mctx };
pure r.expr

/--
  Auxiliary method for creating fresh binder names.
  Do not confuse with the method for creating fresh free/meta variable ids. -/
def mkFreshAnonymousName : TermElabM Name := do
s ← get;
let anonymousIdx := s.anonymousIdx;
modify $ fun s => { s with anonymousIdx := s.anonymousIdx + 1 };
pure $ (`_a).appendIndexAfter anonymousIdx

/--
  Auxiliary method for creating a `Syntax.ident` containing
  a fresh name. This method is intended for creating fresh binder names.
  It is just a thin layer on top of `mkFreshAnonymousName`. -/
def mkFreshAnonymousIdent (ref : Syntax) : TermElabM Syntax := do
n ← mkFreshAnonymousName;
pure $ mkIdentFrom ref n

/--
  Auxiliary method for creating binder names for local instances.
  Users expect them to be named as `_inst_<idx>`. -/
def mkFreshInstanceName : TermElabM Name := do
s ← get;
let instIdx := s.instImplicitIdx;
modify $ fun s => { s with instImplicitIdx := s.instImplicitIdx + 1 };
pure $ (`_inst).appendIndexAfter instIdx

private partial def hasCDot : Syntax → Bool
| Syntax.node k args =>
  if k == `Lean.Parser.Term.paren then false
  else if k == `Lean.Parser.Term.cdot then true
  else args.any hasCDot
| _ => false

/--
  Auxiliary function for expandind the `·` notation.
  The extra state `Array Syntax` contains the new binder names.
  If `stx` is a `·`, we create a fresh identifier, store in the
  extra state, and return it. Otherwise, we just return `stx`. -/
private partial def expandCDot : Syntax → StateT (Array Syntax) MacroM Syntax
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.paren then pure stx
  else if k == `Lean.Parser.Term.cdot then withFreshMacroScope $ do
    id ← `(a);
    modify $ fun s => s.push id;
    pure id
  else do
    args ← args.mapM expandCDot;
    pure $ Syntax.node k args
| stx => pure stx

/--
  Return `some` if succeeded expanding `·` notation occurring in
  the given syntax. Otherwise, return `none`.
  Examples:
  - `· + 1` => `fun _a_1 => _a_1 + 1`
  - `f · · b` => `fun _a_1 _a_2 => f _a_1 _a_2 b` -/
def expandCDot? (stx : Syntax) : MacroM (Option Syntax) :=
if hasCDot stx then do
  (newStx, binders) ← (expandCDot stx).run #[];
  `(fun $binders* => $newStx)
else
  pure none

def mkFreshFVarId : TermElabM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { s with ngen := s.ngen.next };
pure id

def withLocalDecl {α} (ref : Syntax) (n : Name) (binderInfo : BinderInfo) (type : Expr) (k : Expr → TermElabM α) : TermElabM α := do
fvarId ← mkFreshFVarId;
ctx ← read;
let lctx       := ctx.lctx.mkLocalDecl fvarId n type binderInfo;
let localInsts := ctx.localInstances;
let fvar       := mkFVar fvarId;
c? ← isClass ref type;
match c? with
| some c => adaptReader (fun (ctx : Context) => { ctx with lctx := lctx, localInstances := localInsts.push { className := c, fvar := fvar } }) $ k fvar
| none   => adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $ k fvar

def withLetDecl {α} (ref : Syntax) (n : Name) (type : Expr) (val : Expr) (k : Expr → TermElabM α) : TermElabM α := do
fvarId ← mkFreshFVarId;
ctx ← read;
let lctx       := ctx.lctx.mkLetDecl fvarId n type val;
let localInsts := ctx.localInstances;
let fvar       := mkFVar fvarId;
c? ← isClass ref type;
match c? with
| some c => adaptReader (fun (ctx : Context) => { ctx with lctx := lctx, localInstances := localInsts.push { className := c, fvar := fvar } }) $ k fvar
| none   => adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $ k fvar

def throwTypeMismatchError {α} (ref : Syntax) (expectedType : Expr) (eType : Expr) (e : Expr)
    (f? : Option Expr := none) (extraMsg? : Option MessageData := none) : TermElabM α :=
let extraMsg : MessageData := match extraMsg? with
  | none          => Format.nil
  | some extraMsg => Format.line ++ extraMsg;
match f? with
| none =>
  let msg : MessageData :=
    "type mismatch" ++ indentExpr e
    ++ Format.line ++ "has type" ++ indentExpr eType
    ++ Format.line ++ "but it is expected to have type" ++ indentExpr expectedType
    ++ extraMsg;
  throwError ref msg
| some f => do
  env ← getEnv; mctx ← getMCtx; lctx ← getLCtx; opts ← getOptions;
  throwError ref $ Meta.Exception.mkAppTypeMismatchMessage f e { env := env, mctx := mctx, lctx := lctx, opts := opts } ++ extraMsg

@[inline] def withoutMacroStackAtErr {α} (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStackAtErr := false }) x

/- Try to synthesize metavariable using type class resolution.
   This method assumes the local context and local instances of `instMVar` coincide
   with the current local context and local instances.
   Return `true` if the instance was synthesized successfully, and `false` if
   the instance contains unassigned metavariables that are blocking the type class
   resolution procedure. Throw an exception if resolution or assignment irrevocably fails. -/
def synthesizeInstMVarCore (ref : Syntax) (instMVar : MVarId) : TermElabM Bool := do
instMVarDecl ← getMVarDecl instMVar;
let type := instMVarDecl.type;
type ← instantiateMVars ref type;
result ← trySynthInstance ref type;
match result with
| LOption.some val => do
  condM (isExprMVarAssigned instMVar)
    (do oldVal ← instantiateMVars ref (mkMVar instMVar);
        unlessM (isDefEq ref oldVal val) $
          throwError ref $
            "synthesized type class instance is not definitionally equal to expression "
            ++ "inferred by typing rules, synthesized" ++ indentExpr val
            ++ Format.line ++ "inferred" ++ indentExpr oldVal)
    (assignExprMVar instMVar val);
  pure true
| LOption.undef    => pure false -- we will try later
| LOption.none     => throwError ref ("failed to synthesize instance" ++ indentExpr type)

/--
  Try to apply coercion to make sure `e` has type `expectedType`.
  Relevant definitions:
  ```
  class CoeT (α : Sort u) (a : α) (β : Sort v)
  abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β
  ``` -/
def tryCoe (ref : Syntax) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr :=
condM (isDefEq ref expectedType eType) (pure e) $ do
u ← getLevel ref eType;
v ← getLevel ref expectedType;
let coeTInstType := mkAppN (mkConst `CoeT [u, v]) #[eType, e, expectedType];
mvar ← mkFreshExprMVar ref coeTInstType MetavarKind.synthetic;
let eNew := mkAppN (mkConst `coe [u, v]) #[eType, expectedType, e, mvar];
let mvarId := mvar.mvarId!;
catch
  (withoutMacroStackAtErr $ do
    unlessM (synthesizeInstMVarCore ref mvarId) $
      registerSyntheticMVar ref mvarId (SyntheticMVarKind.coe expectedType eType e f?);
    pure eNew)
  (fun ex =>
    match ex with
    | Exception.ex (Elab.Exception.error errMsg) => throwTypeMismatchError ref expectedType eType e f? errMsg.data
    | _ => throwTypeMismatchError ref expectedType eType e f?)

private def isTypeApp? (ref : Syntax) (type : Expr) : TermElabM (Option (Expr × Expr)) := do
type ← withReducible $ whnf ref type;
match type with
| Expr.app m α _ => pure (some (m, α))
| _              => pure none

structure IsMonadResult :=
(m    : Expr)
(α    : Expr)
(inst : Expr)

private def isMonad? (ref : Syntax) (type : Expr) : TermElabM (Option IsMonadResult) := do
type ← withReducible $ whnf ref type;
match type with
| Expr.app m α _ =>
  catch
    (do
      monadType ← mkAppM ref `Monad #[m];
      result    ← trySynthInstance ref monadType;
      match result with
      | LOption.some inst => pure (some { m := m, α := α, inst := inst })
      | _                 => pure none)
    (fun _ => pure none)
| _              => pure none

def synthesizeInst (ref : Syntax) (type : Expr) : TermElabM Expr := do
type ← instantiateMVars ref type;
result ← trySynthInstance ref type;
match result with
| LOption.some val => pure val
| LOption.undef    => throwError ref ("failed to synthesize instance" ++ indentExpr type)
| LOption.none     => throwError ref ("failed to synthesize instance" ++ indentExpr type)

/--
  Try to coerce `a : α` into `m β` by first coercing `a : α` into ‵β`, and then using `pure`.
  The method is only applied if the head of `α` nor ‵β` is not a metavariable. -/
private def tryPureCoe? (ref : Syntax) (m β α a : Expr) : TermElabM (Option Expr) :=
if β.getAppFn.isMVar || α.getAppFn.isMVar then pure none
else catch
 (do
   aNew ← tryCoe ref β α a none;
   aNew ← liftMetaM ref $ Meta.mkPure m aNew;
   pure $ some aNew)
 (fun _ => pure none)

/-
Try coercions and monad lifts to make sure `e` has type `expectedType`.

If `expectedType` is of the form `n β` where `n` is a Monad, we try monad lifts and other extensions.
Otherwise, we just use the basic `tryCoe`.

Extensions for monads.

Given an expected type of the form `n β`, if `eType` is of the form `α`

1 - Try to coerce ‵α` into ‵β`, and use `pure` to lift it to `n α`.

If `eType` is of the form `m α`. We use the following approaches.

1- Try to unify `n` and `m`. If it succeeds, then we rely on `tryCoe`, and
   the instances
   ```
   instance coeMethod {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] : Coe (m α) (m β)
   instance pureCoeDepProp {m : Type → Type v} [HasPure m] {p : Prop} [Decidable p] : CoeDep (m Prop) (pure p) (m Bool)
   ```

2- If there is monad lift from `m` to `n` and we can unify `α` and `β`, we use
  ```
  liftM : ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [self : HasMonadLiftT m n] {α : Type u_1}, m α → n α
  ```

3- If there is a monad lif from `m` to `n` and a coercion from `α` to `β`, we use
  ```
  liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [HasMonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β
  ```

Note that approach 3 does not subsume 1 because it is only applicable if there is a coercion from `α` to `β` for all values in `α`.
This is not the case for example for `pure $ x > 0` when the expected type is `IO Bool`. The given type is `IO Prop`, and
we only have a coercion from decidable propositions.  Approach 1 works because it constructs the coercion `CoeT (m Prop) (pure $ x > 0) (m Bool)`
using the instance `pureCoeDepProp`.

Note that, approach 2 is more powerful than `tryCoe`.
Recall that type class resolution never assigns metavariables created by other modules.
Now, consider the following scenario
```lean
def g (x : Nat) : IO Nat := ...
deg h (x : Nat) : StateT Nat IO Nat := do
v ← g x;
IO.Println v;
...
```
Let's assume there is no other occurrence of `v` in `h`.
Thus, we have that the expected of `g x` is `StateT Nat IO ?α`,
and the given type is `IO Nat`. So, even if we add a coercion.
```
instance {α m n} [HasLiftT m n] {α} : Coe (m α) (n α) := ...
```
It is not applicable because TC would have to assign `?α := Nat`.
On the other hand, TC can easily solve `[HasLiftT IO (StateT Nat IO)]`
since this goal does not contain any metavariables. And then, we
convert `g x` into `liftM $ g x`.
-/
def tryLiftAndCoe (ref : Syntax) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Expr := do
eType ← instantiateMVars ref eType;
some ⟨n, β, monadInst⟩ ← isMonad? ref expectedType | tryCoe ref expectedType eType e f?;
β ← instantiateMVars ref β;
eNew? ← tryPureCoe? ref n β eType e;
match eNew? with
| some eNew => pure eNew
| none      => do
some (m, α) ← isTypeApp? ref eType | tryCoe ref expectedType eType e f?;
condM (isDefEq ref m n) (tryCoe ref expectedType eType e f?) $
  catch
    (do
      -- Construct lift from `m` to `n`
      hasMonadLiftType ← mkAppM ref `HasMonadLiftT #[m, n];
      hasMonadLiftVal  ← synthesizeInst ref hasMonadLiftType;
      u_1 ← getDecLevel ref α;
      u_2 ← getDecLevel ref eType;
      u_3 ← getDecLevel ref expectedType;
      let eNew := mkAppN (Lean.mkConst `liftM [u_1, u_2, u_3]) #[m, n, hasMonadLiftVal, α, e];
      eNewType ← inferType ref eNew;
      condM (isDefEq ref expectedType eNewType)
        (pure eNew) -- approach 2 worked
        (do
          u ← getLevel ref α;
          v ← getLevel ref β;
          let coeTInstType := Lean.mkForall `a BinderInfo.default α $ mkAppN (mkConst `CoeT [u, v]) #[α, mkBVar 0, β];
          coeTInstVal ← synthesizeInst ref coeTInstType;
          let eNew := mkAppN (Lean.mkConst `liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, hasMonadLiftVal, coeTInstVal, monadInst, e];
          eNewType ← inferType ref eNew;
          condM (isDefEq ref expectedType eNewType)
            (pure eNew) -- approach 3 worked
            (throwTypeMismatchError ref expectedType eType e f?)))
    (fun _ => throwTypeMismatchError ref expectedType eType e f?)

/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.

  Argument `f?` is used only for generating error messages. -/
def ensureHasTypeAux (ref : Syntax) (expectedType? : Option Expr) (eType : Expr) (e : Expr) (f? : Option Expr := none) : TermElabM Expr :=
match expectedType? with
| none              => pure e
| some expectedType =>
  /-
    Recall that constant approximation is used to solve constraint of the form
    ```
    ?m t =?= s
    ```
    where `t` is an arbitrary term, by assigning `?m := fun _ => s`
    This approximation when not used carefully produces bad solutions, and may prevent coercions from being tried.
    For example, consider the term `pure (x > 0)` with inferred type `?m Prop` and expected type `IO Bool`. In this situation, the
    elaborator generates the unification constraint
    ```
    ?m Prop =?= IO Bool
    ```
    It is not a higher-order pattern, not first-order approximation is applicable. However, constant approximation
    produces the bogus solution `?m := fun _ => IO Bool`, and prevents the system from using the coercion from
    the decidable proposition `x > 0` to `Bool`.

    On the other hand, the constant approximation is desirable for elaborating the term
    ```
    let f (x : _) := pure 0; f ()
    ```
    with expected type `StateT Nat Id Nat`.
    In this example, the following unification contraint is generated.
    ```
    ?m () (?n ()) =?= StateT Nat Id Nat
    ```
    It is not a higher-order pattern, and first-order approximation fails.
    However, constant approximation solves it by assigning
    ```
    ?m := fun _ => StateT Nat Id
    ?n := fun _ => Nat
    ```
    Note that `f`s type is `(x : ?α) -> ?m x (?n x)`. The metavariables `?m` and `?n` may depend on `x`.

    The `isDefEqNoConstantApprox` fails to unify the expected and inferred types. Then, `tryLiftAndCoe` first tries
    the monadic extensions, and then falls back to `isDefEq` which enables all approximations.
  -/
  condM (isDefEqNoConstantApprox ref eType expectedType)
    (pure e)
    (tryLiftAndCoe ref expectedType eType e f?)

/--
  If `expectedType?` is `some t`, then ensure `t` and type of `e` are definitionally equal.
  If they are not, then try coercions. -/
def ensureHasType (ref : Syntax) (expectedType? : Option Expr) (e : Expr) : TermElabM Expr :=
match expectedType? with
| none => pure e
| _    => do eType ← inferType ref e; ensureHasTypeAux ref expectedType? eType e

private def exceptionToSorry (ref : Syntax) (errMsg : Message) (expectedType? : Option Expr) : TermElabM Expr := do
expectedType : Expr ← match expectedType? with
  | none              => mkFreshTypeMVar ref
  | some expectedType => pure expectedType;
u ← getLevel ref expectedType;
-- TODO: should be `(sorryAx.{$u} $expectedType true) when we support antiquotations at that place
let syntheticSorry := mkApp2 (mkConst `sorryAx [u]) expectedType (mkConst `Bool.true);
unless errMsg.data.hasSyntheticSorry $ logMessage errMsg;
pure syntheticSorry

/-- If `mayPostpone == true`, throw `Expection.postpone`. -/
def tryPostpone : TermElabM Unit := do
ctx ← read;
when ctx.mayPostpone $ throw Exception.postpone

/-- If `mayPostpone == true` and `e`'s head is a metavariable, throw `Exception.postpone`. -/
def tryPostponeIfMVar (e : Expr) : TermElabM Unit := do
when e.getAppFn.isMVar $ tryPostpone

def tryPostponeIfNoneOrMVar (e? : Option Expr) : TermElabM Unit :=
match e? with
| some e => tryPostponeIfMVar e
| none   => tryPostpone

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
trace `Elab.postpone stx $ fun _ => stx ++ " : " ++ expectedType?;
mvar ← mkFreshExprMVar stx expectedType? MetavarKind.syntheticOpaque;
ctx ← read;
registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed ctx.macroStack);
pure mvar

/-
  Helper function for `elabTerm` is tries the registered elaboration functions for `stxNode` kind until it finds one that supports the syntax or
  an error is found. -/
private def elabUsingElabFnsAux (s : State) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List TermElab → TermElabM Expr
| []                => do
  let refFmt := stx.prettyPrint;
  throwError stx ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catch (elabFn stx expectedType?)
  (fun ex => match ex with
    | Exception.ex (Elab.Exception.error errMsg)    => do ctx ← read; if ctx.errToSorry then exceptionToSorry stx errMsg expectedType? else throw ex
    | Exception.ex Elab.Exception.unsupportedSyntax => do set s; elabUsingElabFnsAux elabFns
    | Exception.postpone          =>
      if catchExPostpone then do
        /- If `elab` threw `Exception.postpone`, we reset any state modifications.
           For example, we want to make sure pending synthetic metavariables created by `elab` before
           it threw `Exception.postpone` are discarded.
           Note that we are also discarding the messages created by `elab`.

           For example, consider the expression.
           `((f.x a1).x a2).x a3`
           Now, suppose the elaboration of `f.x a1` produces an `Exception.postpone`.
           Then, a new metavariable `?m` is created. Then, `?m.x a2` also throws `Exception.postpone`
           because the type of `?m` is not yet known. Then another, metavariable `?n` is created, and
          finally `?n.x a3` also throws `Exception.postpone`. If we did not restore the state, we would
          keep "dead" metavariables `?m` and `?n` on the pending synthetic metavariable list. This is
          wasteful because when we resume the elaboration of `((f.x a1).x a2).x a3`, we start it from scratch
          and new metavariables are created for the nested functions. -/
          set s;
          postponeElabTerm stx expectedType?
        else
          throw ex)

def elabUsingElabFns (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool) : TermElabM Expr := do
s ← get;
let table := (termElabAttribute.ext.getState s.env).table;
let k := stx.getKind;
match table.find? k with
| some elabFns => elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
| none         => throwError stx ("elaboration function for '" ++ toString k ++ "' has not been implemented")

instance : MonadMacroAdapter TermElabM :=
{ getEnv                 := getEnv,
  getCurrMacroScope      := getCurrMacroScope,
  getNextMacroScope      := do s ← get; pure s.nextMacroScope,
  setNextMacroScope      := fun next => modify $ fun s => { s with nextMacroScope := next },
  throwError             := @throwError,
  throwUnsupportedSyntax := @throwUnsupportedSyntax}

private def isExplicit (stx : Syntax) : Bool :=
match_syntax stx with
| `(@$f) => true
| _      => false

private def isExplicitApp (stx : Syntax) : Bool :=
stx.getKind == `Lean.Parser.Term.app && isExplicit (stx.getArg 0)

/--
  Return true if `stx` if a lambda abstraction containing a `{}` or `[]` binder annotation.
  Example: `fun {α} (a : α) => a` -/
private def isLambdaWithImplicit (stx : Syntax) : Bool :=
match_syntax stx with
| `(fun $binders* => $body) => binders.any $ fun b => b.isOfKind `Lean.Parser.Term.implicitBinder || b.isOfKind `Lean.Parser.Term.instBinder
| _                         => false

partial def dropTermParens : Syntax → Syntax | stx =>
match_syntax stx with
| `(($stx)) => dropTermParens stx
| _         => stx

/-- Block usage of implicit lambdas if `stx` is `@f` or `@f arg1 ...` or `fun` with an implicit binder annotation. -/
def blockImplicitLambda (stx : Syntax) : Bool :=
let stx := dropTermParens stx;
isExplicit stx || isExplicitApp stx || isLambdaWithImplicit stx

/--
  Return normalized expected type if it is of the form `{a : α} → β` or `[a : α] → β` and
  `blockImplicitLambda stx` is not true, else return `none`. -/
def useImplicitLambda? (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Option Expr) :=
if blockImplicitLambda stx then pure none
else match expectedType? with
  | some expectedType => do
    expectedType ← whnfForall stx expectedType;
    match expectedType with
    | Expr.forallE _ _ _ c => pure $ if c.binderInfo.isExplicit then none else some expectedType
    | _                    => pure $ none
  | _         => pure $ none

def elabImplicitLambdaAux (stx : Syntax) (catchExPostpone : Bool) (expectedType : Expr) (fvars : Array Expr) : TermElabM Expr := do
body ← elabUsingElabFns stx expectedType catchExPostpone;
-- body ← ensureHasType stx expectedType body;
r ← mkLambda stx fvars body;
trace `Elab.implicitForall stx $ fun _ => r;
pure r

partial def elabImplicitLambda (stx : Syntax) (catchExPostpone : Bool) : Expr → Array Expr → TermElabM Expr
| type@(Expr.forallE n d b c), fvars =>
  if c.binderInfo.isExplicit then
    elabImplicitLambdaAux stx catchExPostpone type fvars
  else withFreshMacroScope $ do
    n ← MonadQuotation.addMacroScope n;
    withLocalDecl stx n c.binderInfo d $ fun fvar => do
      type ← whnfForall stx (b.instantiate1 fvar);
      elabImplicitLambda type (fvars.push fvar)
| type, fvars =>
  elabImplicitLambdaAux stx catchExPostpone type fvars

/- Main loop for `elabTerm` -/
partial def elabTermAux (expectedType? : Option Expr) (catchExPostpone : Bool) (implicitLambda : Bool) : Syntax → TermElabM Expr
| stx => withFreshMacroScope $ withIncRecDepth stx $ do
  trace `Elab.step stx $ fun _ => expectedType? ++ " " ++ stx;
  s ← get;
  stxNew? ← catch
    (do newStx ← adaptMacro (getMacros s.env) stx; pure (some newStx))
    (fun ex => match ex with
      | Exception.ex Elab.Exception.unsupportedSyntax => pure none
      | _                                             => throw ex);
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTermAux stxNew
  | _ => do
    implicit? ← if implicitLambda then useImplicitLambda? stx expectedType? else pure none;
    match implicit? with
    | some expectedType => elabImplicitLambda stx catchExPostpone expectedType #[]
    | none              => elabUsingElabFns stx expectedType? catchExPostpone

/--
  Main function for elaborating terms.
  It extracts the elaboration methods from the environment using the node kind.
  Recall that the environment has a mapping from `SyntaxNodeKind` to `TermElab` methods.
  It creates a fresh macro scope for executing the elaboration method.
  All unlogged trace messages produced by the elaboration method are logged using
  the position information at `stx`. If the elaboration method throws an `Exception.error` and `errToSorry == true`,
  the error is logged and a synthetic sorry expression is returned.
  If the elaboration throws `Exception.postpone` and `catchExPostpone == true`,
  a new synthetic metavariable of kind `SyntheticMVarKind.postponed` is created, registered,
  and returned.
  The option `catchExPostpone == false` is used to implement `resumeElabTerm`
  to prevent the creation of another synthetic metavariable when resuming the elaboration. -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) : TermElabM Expr :=
elabTermAux expectedType? catchExPostpone true stx

def elabTermWithoutImplicitLambdas (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) : TermElabM Expr := do
elabTermAux expectedType? catchExPostpone false stx

/-- Adapt a syntax transformation to a regular, term-producing elaborator. -/
def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab :=
fun stx expectedType? => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ elabTerm stx' expectedType?

@[inline] def withLCtx {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : TermElabM α) : TermElabM α :=
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx, localInstances := localInsts }) x

def resetSynthInstanceCache : TermElabM Unit :=
modify $ fun s => { s with cache := { s.cache with synthInstance := {} } }

@[inline] def resettingSynthInstanceCache {α} (x : TermElabM α) : TermElabM α := do
s ← get;
let savedSythInstance := s.cache.synthInstance;
resetSynthInstanceCache;
finally x (modify $ fun s => { s with cache := { s.cache with synthInstance := savedSythInstance } })

@[inline] def resettingSynthInstanceCacheWhen {α} (b : Bool) (x : TermElabM α) : TermElabM α :=
if b then resettingSynthInstanceCache x else x

/--
  Execute `x` using the given metavariable's `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext {α} (mvarId : MVarId) (x : TermElabM α) : TermElabM α := do
mvarDecl  ← getMVarDecl mvarId;
ctx       ← read;
let needReset := ctx.localInstances == mvarDecl.localInstances;
withLCtx mvarDecl.lctx mvarDecl.localInstances $ resettingSynthInstanceCacheWhen needReset x

def mkInstMVar (ref : Syntax) (type : Expr) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
unlessM (synthesizeInstMVarCore ref mvarId) $
  registerSyntheticMVar ref mvarId SyntheticMVarKind.typeClass;
pure mvar

/-
  Relevant definitions:
  ```
  class CoeSort (α : Sort u) (β : outParam (Sort v))
  abbrev coeSort {α : Sort u} {β : Sort v} (a : α) [CoeSort α β] : β
  ``` -/
private def tryCoeSort (ref : Syntax) (α : Expr) (a : Expr) : TermElabM Expr := do
β ← mkFreshTypeMVar ref;
u ← getLevel ref α;
v ← getLevel ref β;
let coeSortInstType := mkAppN (Lean.mkConst `CoeSort [u, v]) #[α, β];
mvar ← mkFreshExprMVar ref coeSortInstType MetavarKind.synthetic;
let mvarId := mvar.mvarId!;
catch
  (withoutMacroStackAtErr $ condM (synthesizeInstMVarCore ref mvarId)
    (pure $ mkAppN (Lean.mkConst `coeSort [u, v]) #[α, β, a, mvar])
    (throwError ref "type expected"))
  (fun ex =>
    match ex with
    | Exception.ex (Elab.Exception.error errMsg) => throwError ref ("type expected" ++ Format.line ++ errMsg.data)
    | _ => throwError ref "type expected")

/--
  Make sure `e` is a type by inferring its type and making sure it is a `Expr.sort`
  or is unifiable with `Expr.sort`, or can be coerced into one. -/
def ensureType (ref : Syntax) (e : Expr) : TermElabM Expr :=
condM (isType ref e)
  (pure e)
  (do
    eType ← inferType ref e;
    u ← mkFreshLevelMVar ref;
    condM (isDefEq ref eType (mkSort u))
      (pure e)
      (tryCoeSort ref eType e))

/-- Elaborate `stx` and ensure result is a type. -/
def elabType (stx : Syntax) : TermElabM Expr := do
u ← mkFreshLevelMVar stx;
type ← elabTerm stx (mkSort u);
ensureType stx type

def addDecl (ref : Syntax) (decl : Declaration) : TermElabM Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error kex => do opts ← getOptions; throwError ref (kex.toMessageData opts)

def compileDecl (ref : Syntax) (decl : Declaration) : TermElabM Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env    => setEnv env
| Except.error kex => throwError ref (kex.toMessageData opts)

private partial def mkAuxNameAux (env : Environment) (base : Name) : Nat → Name
| i =>
  let candidate := base.appendIndexAfter i;
  if env.contains candidate then
    mkAuxNameAux (i+1)
  else
    candidate

def mkAuxName (ref : Syntax) (suffix : Name) : TermElabM Name := do
env ← getEnv;
ctx ← read;
match ctx.declName? with
| none          => throwError ref "auxiliary declaration cannot be created when declaration name is not available"
| some declName => pure $ mkAuxNameAux env (declName ++ suffix) 1

/- =======================================
       Builtin elaboration functions
   ======================================= -/

@[builtinTermElab «prop»] def elabProp : TermElab :=
fun _ _ => pure $ mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
if stx.isNone then
  pure levelZero
else
  elabLevel $ stx.getArg 0

@[builtinTermElab «sort»] def elabSort : TermElab :=
fun stx _ => do
  u ← elabOptLevel $ stx.getArg 1;
  pure $ mkSort u

@[builtinTermElab «type»] def elabTypeStx : TermElab :=
fun stx _ => do
  u ← elabOptLevel $ stx.getArg 1;
  pure $ mkSort (mkLevelSucc u)

@[builtinTermElab «hole»] def elabHole : TermElab :=
fun stx expectedType? => mkFreshExprMVar stx expectedType?

@[builtinTermElab «namedHole»] def elabNamedHole : TermElab :=
fun stx expectedType? =>
  let name := stx.getIdAt 1;
  mkFreshExprMVar stx expectedType? MetavarKind.syntheticOpaque name

def mkTacticMVar (ref : Syntax) (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
mvar ← mkFreshExprMVar ref type MetavarKind.syntheticOpaque `main;
let mvarId := mvar.mvarId!;
registerSyntheticMVar ref mvarId $ SyntheticMVarKind.tactic tacticCode;
pure mvar

@[builtinTermElab tacticBlock] def elabTacticBlock : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar stx expectedType (stx.getArg 1)
  | none => throwError stx ("invalid tactic block, expected type has not been provided")

@[builtinTermElab byTactic] def elabByTactic : TermElab :=
fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar stx expectedType (stx.getArg 1)
  | none => throwError stx ("invalid 'by' tactic, expected type has not been provided")

/-- Main loop for `mkPairs`. -/
private partial def mkPairsAux (elems : Array Syntax) : Nat → Syntax → MacroM Syntax
| i, acc =>
  if i > 0 then do
    let i    := i - 1;
    let elem := elems.get! i;
    acc ← `(Prod.mk $elem $acc);
    mkPairsAux i acc
  else
    pure acc

/-- Return syntax `Prod.mk elems[0] (Prod.mk elems[1] ... (Prod.mk elems[elems.size - 2] elems[elems.size - 1])))` -/
def mkPairs (elems : Array Syntax) : MacroM Syntax :=
mkPairsAux elems (elems.size - 1) elems.back

/--
  Try to expand `·` notation, and if successful elaborate result.
  This method is used to elaborate the Lean parentheses notation.
  Recall that in Lean the `·` notation must be surrounded by parentheses.
  We may change this is the future, but right now, here are valid examples
  - `(· + 1)`
  - `(f ⟨·, 1⟩ ·)`
  - `(· + ·)`
  - `(f · a b)` -/
private def elabCDot (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
stx? ← liftMacroM $ expandCDot? stx;
match stx? with
| some stx' => withMacroExpansion stx stx' (elabTerm stx' expectedType?)
| none      => elabTerm stx expectedType?

@[builtinTermElab paren] def elabParen : TermElab :=
fun stx expectedType? =>
  let ref := stx;
  match_syntax ref with
  | `(())           => pure $ Lean.mkConst `Unit.unit
  | `(($e : $type)) => do
    type ← elabType type;
    e ← elabCDot e type;
    ensureHasType ref type e
  | `(($e))         => elabCDot e expectedType?
  | `(($e, $es*))   => do
    pairs ← liftMacroM $ mkPairs (#[e] ++ es.getEvenElems);
    withMacroExpansion stx pairs (elabTerm pairs expectedType?)
  | _ => throwError stx "unexpected parentheses notation"

@[builtinTermElab «listLit»] def elabListLit : TermElab :=
fun stx expectedType? => do
  let openBkt  := stx.getArg 0;
  let args     := stx.getArg 1;
  let closeBkt := stx.getArg 2;
  let consId   := mkTermIdFrom openBkt `List.cons;
  let nilId    := mkTermIdFrom closeBkt `List.nil;
  let newStx   := args.foldSepRevArgs (fun arg r => mkAppStx consId #[arg, r]) nilId;
  withMacroExpansion stx newStx $ elabTerm newStx expectedType?

@[builtinTermElab «arrayLit»] def elabArrayLit : TermElab :=
fun stx expectedType? => do
  match_syntax stx with
  | `(#[$args*]) => do
    newStx ← `(List.toArray [$args*]);
    withMacroExpansion stx newStx (elabTerm newStx expectedType?)
  | _ => throwError stx "unexpected array literal syntax"

private partial def resolveLocalNameAux (lctx : LocalContext) : Name → List String → Option (Expr × List String)
| n, projs =>
  match lctx.findFromUserName? n with
  | some decl => some (decl.toExpr, projs)
  | none      => match n with
    | Name.str pre s _ => resolveLocalNameAux pre (s::projs)
    | _                => none

private def resolveLocalName (n : Name) : TermElabM (Option (Expr × List String)) := do
lctx ← getLCtx;
pure $ resolveLocalNameAux lctx n []

/- Return true iff `stx` is a `Term.id`, and it is local variable. -/
def isLocalTermId? (stx : Syntax) (relaxed : Bool := false) : TermElabM (Option Expr) :=
match stx.isTermId? relaxed with
| some (Syntax.ident _ _ val _, _) => do
  r? ← resolveLocalName val;
  match r? with
  | some (fvar, []) => pure (some fvar)
  | _               => pure none
| _ => pure none

private def mkFreshLevelMVars (ref : Syntax) (num : Nat) : TermElabM (List Level) :=
num.foldM (fun _ us => do u ← mkFreshLevelMVar ref; pure $ u::us) []

/--
  Create an `Expr.const` using the given name and explicit levels.
  Remark: fresh universe metavariables are created if the constant has more universe
  parameters than `explicitLevels`. -/
def mkConst (ref : Syntax) (constName : Name) (explicitLevels : List Level := []) : TermElabM Expr := do
env ← getEnv;
match env.find? constName with
| none       => throwError ref ("unknown constant '" ++ constName ++ "'")
| some cinfo =>
  if explicitLevels.length > cinfo.lparams.length then
    throwError ref ("too many explicit universe levels")
  else do
    let numMissingLevels := cinfo.lparams.length - explicitLevels.length;
    us ← mkFreshLevelMVars ref numMissingLevels;
    pure $ Lean.mkConst constName (explicitLevels ++ us)

private def mkConsts (ref : Syntax) (candidates : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
env ← getEnv;
candidates.foldlM
  (fun result ⟨constName, projs⟩ => do
    -- TODO: better suppor for `mkConst` failure. We may want to cache the failures, and report them if all candidates fail.
    const ← mkConst ref constName explicitLevels;
    pure $ (const, projs) :: result)
  []

def resolveGlobalName (n : Name) : TermElabM (List (Name × List String)) := do
env ← getEnv;
currNamespace ← getCurrNamespace;
openDecls ← getOpenDecls;
pure (Lean.Elab.resolveGlobalName env currNamespace openDecls n)

def resolveName (ref : Syntax) (n : Name) (preresolved : List (Name × List String)) (explicitLevels : List Level) : TermElabM (List (Expr × List String)) := do
result? ← resolveLocalName n;
match result? with
| some (e, projs) => do
  unless explicitLevels.isEmpty $
    throwError ref ("invalid use of explicit universe parameters, '" ++ toString e.fvarId! ++ "' is a local");
  pure [(e, projs)]
| none =>
  let process (candidates : List (Name × List String)) : TermElabM (List (Expr × List String)) := do {
    when candidates.isEmpty $ do {
      mainModule ← getMainModule;
      let view := extractMacroScopes n;
      throwError ref ("unknown identifier '" ++ view.format mainModule ++ "'")
    };
    mkConsts ref candidates explicitLevels
  };
  if preresolved.isEmpty then do
    r ← resolveGlobalName n;
    process r
  else
    process preresolved

@[builtinTermElab cdot] def elabBadCDot : TermElab :=
fun stx _ => throwError stx "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

/-
  A raw literal is not a valid term, but it is nice to have a handler for them because it allows `macros` to insert them into terms.

  TODO: check whether we still need wrapper nodes around literals. -/
@[builtinTermElab strLit] def elabRawStrLit : TermElab :=
fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwError stx "ill-formed syntax"

@[builtinTermElab str] def elabStr : TermElab :=
fun stx expectedType? => elabRawStrLit (stx.getArg 0) expectedType?

/- See `elabRawStrLit` -/
@[builtinTermElab numLit] def elabRawNumLit : TermElab :=
fun stx expectedType? => do
  let ref := stx;
  val ← match stx.isNatLit? with
    | some val => pure (mkNatLit val)
    | none     => throwError stx "ill-formed syntax";
  typeMVar ← mkFreshTypeMVar ref MetavarKind.synthetic;
  registerSyntheticMVar ref typeMVar.mvarId! (SyntheticMVarKind.withDefault (Lean.mkConst `Nat));
  match expectedType? with
  | some expectedType => do _ ← isDefEq ref expectedType typeMVar; pure ()
  | _                 => pure ();
  u ← getLevel ref typeMVar;
  u ← decLevel ref u;
  mvar ← mkInstMVar ref (mkApp (Lean.mkConst `HasOfNat [u]) typeMVar);
  pure $ mkApp3 (Lean.mkConst `HasOfNat.ofNat [u]) typeMVar mvar val

@[builtinTermElab num] def elabNum : TermElab :=
fun stx expectedType? => elabRawNumLit (stx.getArg 0) expectedType?

/- See `elabRawStrLit` -/
@[builtinTermElab charLit] def elabRawCharLit : TermElab :=
fun stx _ => do
  match stx.isCharLit? with
  | some val => pure $ mkApp (Lean.mkConst `Char.ofNat) (mkNatLit val.toNat)
  | none     => throwError stx "ill-formed syntax"

@[builtinTermElab char] def elabChar : TermElab :=
fun stx expectedType? => elabRawCharLit (stx.getArg 0) expectedType?

@[builtinTermElab quotedName] def elabQuotedName : TermElab :=
fun stx _ =>
  match (stx.getArg 0).isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwError stx "ill-formed syntax"

instance MetaHasEval {α} [MetaHasEval α] : MetaHasEval (TermElabM α) :=
⟨fun env opts x _ => do
  let ctx : Context := {
    config        := { opts := opts },
    fileName      := "<TermElabM>",
    fileMap       := arbitrary _,
    cmdPos        := 0,
    currNamespace := Name.anonymous,
    currRecDepth  := 0,
    maxRecDepth   := getMaxRecDepth opts
  };
  let showMessages (s : State) : IO Unit := do {
    s.messages.forM $ fun m => IO.println $ format m
  };
  match x ctx { env := env } with
  | EStateM.Result.ok a s => do
    showMessages s;
    MetaHasEval.eval s.env opts a
  | EStateM.Result.error (Exception.ex (Elab.Exception.error err)) s => do
    showMessages s;
    throw (IO.userError (toString (format err)))
  | EStateM.Result.error (Exception.ex Elab.Exception.unsupportedSyntax) s => do
    showMessages s;
    throw (IO.userError "error: unsupported syntax")
  | EStateM.Result.error Exception.postpone s => do
    showMessages s;
    throw (IO.userError "error: elaborator postponed")⟩

end Term

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.postpone;
registerTraceClass `Elab.coe;
registerTraceClass `Elab.debug;
pure ()

export Term (TermElabM)

end Elab
end Lean
