/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Lean.Data.LOption
import Lean.Environment
import Lean.Class
import Lean.ReducibilityAttrs
import Lean.Util.Trace
import Lean.Util.RecDepth
import Lean.Util.Closure
import Lean.Meta.Exception
import Lean.Meta.DiscrTreeTypes
import Lean.Eval

/-
This module provides four (mutually dependent) goodies that are needed for building the elaborator and tactic frameworks.
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
4- Type class resolution.

They are packed into the MetaM monad.
-/

namespace Lean
namespace Meta

inductive TransparencyMode
| all | default | reducible

namespace TransparencyMode
instance : Inhabited TransparencyMode := ⟨TransparencyMode.default⟩

def beq : TransparencyMode → TransparencyMode → Bool
| all,       all       => true
| default,   default   => true
| reducible, reducible => true
| _,         _         => false

instance : HasBeq TransparencyMode := ⟨beq⟩

def hash : TransparencyMode → USize
| all       => 7
| default   => 11
| reducible => 13

instance : Hashable TransparencyMode := ⟨hash⟩

def lt : TransparencyMode → TransparencyMode → Bool
| reducible, default => true
| reducible, all     => true
| default,   all     => true
| _,         _       => false

end TransparencyMode

structure Config :=
(opts               : Options := {})
(foApprox           : Bool    := false)
(ctxApprox          : Bool    := false)
(quasiPatternApprox : Bool    := false)
/- When `constApprox` is set to true,
   we solve `?m t =?= c` using
   `?m := fun _ => c`
   when `?m t` is not a higher-order pattern and `c` is not an application as -/
(constApprox        : Bool    := false)
/-
  When the following flag is set,
  `isDefEq` throws the exeption `Exeption.isDefEqStuck`
  whenever it encounters a constraint `?m ... =?= t` where
  `?m` is read only.
  This feature is useful for type class resolution where
  we may want to notify the caller that the TC problem may be solveable
  later after it assigns `?m`. -/
(isDefEqStuckEx     : Bool    := false)
(debug              : Bool    := false)
(transparency       : TransparencyMode := TransparencyMode.default)

structure ParamInfo :=
(implicit     : Bool      := false)
(instImplicit : Bool      := false)
(hasFwdDeps   : Bool      := false)
(backDeps     : Array Nat := #[])

instance ParamInfo.inhabited : Inhabited ParamInfo := ⟨{}⟩

structure FunInfo :=
(paramInfo  : Array ParamInfo := #[])
(resultDeps : Array Nat       := #[])

structure InfoCacheKey :=
(transparency : TransparencyMode)
(expr         : Expr)
(nargs?       : Option Nat)

namespace InfoCacheKey
instance : Inhabited InfoCacheKey := ⟨⟨arbitrary _, arbitrary _, arbitrary _⟩⟩
instance : Hashable InfoCacheKey :=
⟨fun ⟨transparency, expr, nargs⟩ => mixHash (hash transparency) $ mixHash (hash expr) (hash nargs)⟩
instance : HasBeq InfoCacheKey :=
⟨fun ⟨t₁, e₁, n₁⟩ ⟨t₂, e₂, n₂⟩ => t₁ == t₂ && n₁ == n₂ && e₁ == e₂⟩
end InfoCacheKey

structure Cache :=
(inferType     : PersistentExprStructMap Expr := {})
(funInfo       : PersistentHashMap InfoCacheKey FunInfo := {})
(synthInstance : PersistentHashMap Expr (Option Expr) := {})
(whnfDefault   : PersistentExprStructMap Expr := {}) -- cache for closed terms and `TransparencyMode.default`

structure Context :=
(config         : Config         := {})
(lctx           : LocalContext   := {})
(localInstances : LocalInstances := #[])
(currRecDepth   : Nat)
(maxRecDepth    : Nat)

structure PostponedEntry :=
(lhs       : Level)
(rhs       : Level)

structure State :=
(env            : Environment)
(mctx           : MetavarContext       := {})
(cache          : Cache                := {})
(ngen           : NameGenerator        := {})
(traceState     : TraceState           := {})
(postponed      : PersistentArray PostponedEntry := {})

abbrev MetaM := ReaderT Context (EStateM Exception State)

instance MetaM.inhabited {α} : Inhabited (MetaM α) :=
⟨fun c s => EStateM.Result.error (arbitrary _) s⟩

@[inline] def withIncRecDepth {α} (x : MetaM α) : MetaM α := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throw $ Exception.other maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { ctx with currRecDepth := ctx.currRecDepth + 1 }) x

@[inline] def getLCtx : MetaM LocalContext := do
ctx ← read; pure ctx.lctx

@[inline] def getLocalInstances : MetaM LocalInstances := do
ctx ← read; pure ctx.localInstances

@[inline] def getConfig : MetaM Config := do
ctx ← read; pure ctx.config

@[inline] def getMCtx : MetaM MetavarContext := do
s ← get; pure s.mctx

@[inline] def getEnv : MetaM Environment := do
s ← get; pure s.env

@[inline] def setEnv (env : Environment) : MetaM Unit := do
modify $ fun s => { s with env := env }

def mkWHNFRef : IO (IO.Ref (Expr → MetaM Expr)) :=
IO.mkRef $ fun _ => throw $ Exception.other "whnf implementation was not set"

@[init mkWHNFRef] def whnfRef : IO.Ref (Expr → MetaM Expr) := arbitrary _

def mkInferTypeRef : IO (IO.Ref (Expr → MetaM Expr)) :=
IO.mkRef $ fun _ => throw $ Exception.other "inferType implementation was not set"

@[init mkInferTypeRef] def inferTypeRef : IO.Ref (Expr → MetaM Expr) := arbitrary _

def mkIsExprDefEqAuxRef : IO (IO.Ref (Expr → Expr → MetaM Bool)) :=
IO.mkRef $ fun _ _ => throw $ Exception.other "isDefEq implementation was not set"

@[init mkIsExprDefEqAuxRef] def isExprDefEqAuxRef : IO.Ref (Expr → Expr → MetaM Bool) := arbitrary _

def mkSynthPendingRef : IO (IO.Ref (MVarId → MetaM Bool)) :=
IO.mkRef $ fun _ => pure false

@[init mkSynthPendingRef] def synthPendingRef : IO.Ref (MVarId → MetaM Bool) := arbitrary _

structure MetaExtState :=
(whnf         : Expr → MetaM Expr)
(inferType    : Expr → MetaM Expr)
(isDefEqAux   : Expr → Expr → MetaM Bool)
(synthPending : MVarId → MetaM Bool)

instance MetaExtState.inhabited : Inhabited MetaExtState :=
⟨{ whnf := arbitrary _, inferType := arbitrary _, isDefEqAux := arbitrary _, synthPending := arbitrary _ }⟩

def mkMetaExtension : IO (EnvExtension MetaExtState) :=
registerEnvExtension $ do
  whnf         ← whnfRef.get;
  inferType    ← inferTypeRef.get;
  isDefEqAux   ← isExprDefEqAuxRef.get;
  synthPending ← synthPendingRef.get;
  pure { whnf := whnf, inferType := inferType, isDefEqAux := isDefEqAux, synthPending := synthPending }

@[init mkMetaExtension]
constant metaExt : EnvExtension MetaExtState := arbitrary _

def whnf (e : Expr) : MetaM Expr :=
withIncRecDepth $ do
  env ← getEnv;
  (metaExt.getState env).whnf e

def whnfForall (e : Expr) : MetaM Expr := do
e' ← whnf e;
if e'.isForall then pure e' else pure e

def inferType (e : Expr) : MetaM Expr :=
withIncRecDepth $ do
  env ← getEnv;
  (metaExt.getState env).inferType e

def isExprDefEqAux (t s : Expr) : MetaM Bool :=
withIncRecDepth $ do
  env ← getEnv;
  (metaExt.getState env).isDefEqAux t s

def synthPending (mvarId : MVarId) : MetaM Bool :=
withIncRecDepth $ do
  env ← getEnv;
  (metaExt.getState env).synthPending mvarId

def mkFreshId : MetaM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { s with ngen := s.ngen.next };
pure id

def mkFreshExprMVarAt
    (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (userName : Name := Name.anonymous) (kind : MetavarKind := MetavarKind.natural)
    : MetaM Expr := do
mvarId ← mkFreshId;
modify $ fun s => { s with mctx := s.mctx.addExprMVarDecl mvarId userName lctx localInsts type kind };
pure $ mkMVar mvarId

def mkFreshExprMVar (type : Expr) (userName : Name := Name.anonymous) (kind : MetavarKind := MetavarKind.natural) : MetaM Expr := do
lctx ← getLCtx;
localInsts ← getLocalInstances;
mkFreshExprMVarAt lctx localInsts type userName kind

def mkFreshLevelMVar : MetaM Level := do
mvarId ← mkFreshId;
modify $ fun s => { s with mctx := s.mctx.addLevelMVarDecl mvarId };
pure $ mkLevelMVar mvarId

@[inline] def throwEx {α} (f : ExceptionContext → Exception) : MetaM α := do
ctx ← read;
s ← get;
throw (f { env := s.env, mctx := s.mctx, lctx := ctx.lctx, opts := ctx.config.opts })

def throwBug {α} (b : Bug) : MetaM α :=
throwEx $ Exception.bug b

/-- Execute `x` only in debugging mode. -/
@[inline] private def whenDebugging (x : MetaM Unit) : MetaM Unit := do
ctx ← read;
when ctx.config.debug x

@[inline] def shouldReduceAll : MetaM Bool := do
ctx ← read; pure $ ctx.config.transparency == TransparencyMode.all

@[inline] def shouldReduceReducibleOnly : MetaM Bool := do
ctx ← read; pure $ ctx.config.transparency == TransparencyMode.reducible

@[inline] def getTransparency : MetaM TransparencyMode := do
ctx ← read; pure $ ctx.config.transparency

@[inline] def getOptions : MetaM Options := do
ctx ← read; pure ctx.config.opts

-- Remark: wanted to use `private`, but in C++ parser, `private` declarations do not shadow outer public ones.
-- TODO: fix this bug
@[inline] def isReducible (constName : Name) : MetaM Bool := do
env ← getEnv; pure $ isReducible env constName

@[inline] def withConfig {α} (f : Config → Config) (x : MetaM α) : MetaM α :=
adaptReader (fun (ctx : Context) => { ctx with config := f ctx.config }) x

/-- While executing `x`, ensure the given transparency mode is used. -/
@[inline] def withTransparency {α} (mode : TransparencyMode) (x : MetaM α) : MetaM α :=
withConfig (fun config => { config with transparency := mode }) x

@[inline] def withReducible {α} (x : MetaM α) : MetaM α :=
withTransparency TransparencyMode.reducible x

@[inline] def withAtLeastTransparency {α} (mode : TransparencyMode) (x : MetaM α) : MetaM α :=
withConfig
  (fun config =>
    let oldMode := config.transparency;
    let mode    := if oldMode.lt mode then mode else oldMode;
    { config with transparency := mode })
  x

def getMVarDecl (mvarId : MVarId) : MetaM MetavarDecl := do
mctx ← getMCtx;
match mctx.findDecl? mvarId with
| some d => pure d
| none   => throwEx $ Exception.unknownExprMVar mvarId

def setMVarKind (mvarId : MVarId) (kind : MetavarKind) : MetaM Unit :=
modify $ fun s => { s with mctx := s.mctx.setMVarKind mvarId kind }

def isReadOnlyExprMVar (mvarId : MVarId) : MetaM Bool := do
mvarDecl ← getMVarDecl mvarId;
mctx     ← getMCtx;
pure $ mvarDecl.depth != mctx.depth

def isReadOnlyOrSyntheticOpaqueExprMVar (mvarId : MVarId) : MetaM Bool := do
mvarDecl ← getMVarDecl mvarId;
match mvarDecl.kind with
| MetavarKind.syntheticOpaque => pure true
| _ => do
  mctx ← getMCtx;
  pure $ mvarDecl.depth != mctx.depth

def isReadOnlyLevelMVar (mvarId : MVarId) : MetaM Bool := do
mctx ← getMCtx;
match mctx.findLevelDepth? mvarId with
| some depth => pure $ depth != mctx.depth
| _          => throwEx $ Exception.unknownLevelMVar mvarId

def renameMVar (mvarId : MVarId) (newUserName : Name) : MetaM Unit :=
modify $ fun s => { s with mctx := s.mctx.renameMVar mvarId newUserName }

@[inline] def isExprMVarAssigned (mvarId : MVarId) : MetaM Bool := do
mctx ← getMCtx;
pure $ mctx.isExprAssigned mvarId

@[inline] def getExprMVarAssignment? (mvarId : MVarId) : MetaM (Option Expr) := do
mctx ← getMCtx; pure (mctx.getExprAssignment? mvarId)

def assignExprMVar (mvarId : MVarId) (val : Expr) : MetaM Unit := do
whenDebugging $ whenM (isExprMVarAssigned mvarId) $ throwBug $ Bug.overwritingExprMVar mvarId;
modify $ fun s => { s with mctx := s.mctx.assignExpr mvarId val }

def isDelayedAssigned (mvarId : MVarId) : MetaM Bool := do
mctx ← getMCtx;
pure $ mctx.isDelayedAssigned mvarId

def hasAssignableMVar (e : Expr) : MetaM Bool := do
mctx ← getMCtx;
pure $ mctx.hasAssignableMVar e

def dbgTrace {α} [HasToString α] (a : α) : MetaM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

@[inline] private def getTraceState : MetaM TraceState := do
s ← get; pure s.traceState

def addContext (msg : MessageData) : MetaM MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.withContext { env := s.env, mctx := s.mctx, lctx := ctx.lctx, opts := ctx.config.opts } msg

instance tracer : SimpleMonadTracerAdapter MetaM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { s with traceState := f s.traceState } }

def getConstAux (constName : Name) (exception? : Bool) : MetaM (Option ConstantInfo) := do
env ← getEnv;
match env.find? constName with
| some (info@(ConstantInfo.thmInfo _)) =>
  condM shouldReduceAll (pure (some info)) (pure none)
| some (info@(ConstantInfo.defnInfo _)) =>
  condM shouldReduceReducibleOnly
    (condM (isReducible constName) (pure (some info)) (pure none))
    (pure (some info))
| some info => pure (some info)
| none                                 =>
  if exception? then throwEx $ Exception.unknownConst constName
  else pure none

@[inline] def getConst (constName : Name) : MetaM (Option ConstantInfo) :=
getConstAux constName true

@[inline] def getConstNoEx (constName : Name) : MetaM (Option ConstantInfo) :=
getConstAux constName false

def getConstInfo (constName : Name) : MetaM ConstantInfo := do
env ← getEnv;
match env.find? constName with
| some info => pure info
| none      => throwEx $ Exception.unknownConst constName

def getLocalDecl (fvarId : FVarId) : MetaM LocalDecl := do
lctx ← getLCtx;
match lctx.find? fvarId with
| some d => pure d
| none   => throwEx $ Exception.unknownFVar fvarId

def getFVarLocalDecl (fvar : Expr) : MetaM LocalDecl :=
getLocalDecl fvar.fvarId!

def instantiateMVars (e : Expr) : MetaM Expr :=
if e.hasMVar then
  modifyGet $ fun s =>
    let (e, mctx) := s.mctx.instantiateMVars e;
    (e, { s with mctx := mctx })
else
  pure e

@[inline] private def liftMkBindingM {α} (x : MetavarContext.MkBindingM α) : MetaM α :=
fun ctx s =>
  match x ctx.lctx { mctx := s.mctx, ngen := s.ngen } with
  | EStateM.Result.ok e newS      =>
    EStateM.Result.ok e { s with mctx := newS.mctx, ngen := newS.ngen }
  | EStateM.Result.error (MetavarContext.MkBinding.Exception.revertFailure mctx lctx toRevert decl) newS =>
    EStateM.Result.error
      (Exception.revertFailure toRevert decl { lctx := lctx, mctx := mctx, env := s.env, opts := ctx.config.opts })
      { s with mctx := newS.mctx, ngen := newS.ngen }

def mkForall (xs : Array Expr) (e : Expr) : MetaM Expr :=
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.mkForall xs e

def mkLambda (xs : Array Expr) (e : Expr) : MetaM Expr :=
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.mkLambda xs e

def mkForallUsedOnly (xs : Array Expr) (e : Expr) : MetaM (Expr × Nat) :=
if xs.isEmpty then pure (e, 0) else liftMkBindingM $ MetavarContext.mkForallUsedOnly xs e

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool := false) : MetaM Expr :=
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.elimMVarDeps xs e preserveOrder

/-- Save cache, execute `x`, restore cache -/
@[inline] def savingCache {α} (x : MetaM α) : MetaM α := do
s ← get;
let savedCache := s.cache;
finally x (modify $ fun s => { s with cache := savedCache })

def isClassQuickConst (constName : Name) : MetaM (LOption Name) := do
env ← getEnv;
if isClass env constName then
  pure (LOption.some constName)
else do
  cinfo? ← getConst constName;
  match cinfo? with
  | some _ => pure LOption.undef
  | none   => pure LOption.none

partial def isClassQuick : Expr → MetaM (LOption Name)
| Expr.bvar _ _        => pure LOption.none
| Expr.lit _ _         => pure LOption.none
| Expr.fvar _ _        => pure LOption.none
| Expr.sort _ _        => pure LOption.none
| Expr.lam _ _ _ _     => pure LOption.none
| Expr.letE _ _ _ _ _  => pure LOption.undef
| Expr.proj _ _ _  _   => pure LOption.undef
| Expr.forallE _ _ b _ => isClassQuick b
| Expr.mdata _ e _     => isClassQuick e
| Expr.const n _ _     => isClassQuickConst n
| Expr.mvar mvarId _   => do
  val? ← getExprMVarAssignment? mvarId;
  match val? with
  | some val => isClassQuick val
  | none     => pure LOption.none
| Expr.app f _ _       =>
  match f.getAppFn with
  | Expr.const n _ _  => isClassQuickConst n
  | Expr.lam _ _ _ _  => pure LOption.undef
  | _                 => pure LOption.none
| Expr.localE _ _ _ _ => unreachable!

/-- Reset `synthInstance` cache, execute `x`, and restore cache -/
@[inline] def resettingSynthInstanceCache {α} (x : MetaM α) : MetaM α := do
s ← get;
let savedSythInstance        := s.cache.synthInstance;
modify $ fun s => { s with cache := { s.cache with synthInstance := {} } };
finally x (modify $ fun s => { s with cache := { s.cache with synthInstance := savedSythInstance } })

/-- Add entry `{ className := className, fvar := fvar }` to localInstances,
    and then execute continuation `k`.
    It resets the type class cache using `resettingSynthInstanceCache`. -/
@[inline] def withNewLocalInstance {α} (className : Name) (fvar : Expr) (k : MetaM α) : MetaM α :=
resettingSynthInstanceCache $
  adaptReader
    (fun (ctx : Context) => { ctx with localInstances := ctx.localInstances.push { className := className, fvar := fvar } })
    k

/--
  `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
  using free variables `fvars[j] ... fvars.back`, and execute `k`.

  - `isClassExpensive` is defined later.
  - The type class chache is reset whenever a new local instance is found.
  - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances.
    Thus, each new local instance requires a new `resettingSynthInstanceCache`. -/
@[specialize] partial def withNewLocalInstances {α}
    (isClassExpensive : Expr → MetaM (Option Name))
    (fvars : Array Expr) : Nat → MetaM α → MetaM α
| i, k =>
  if h : i < fvars.size then do
    let fvar := fvars.get ⟨i, h⟩;
    decl ← getFVarLocalDecl fvar;
    c?   ← isClassQuick decl.type;
    match c? with
    | LOption.none   => withNewLocalInstances (i+1) k
    | LOption.undef  => do
      c? ← isClassExpensive decl.type;
      match c? with
      | none   => withNewLocalInstances (i+1) k
      | some c => withNewLocalInstance c fvar $ withNewLocalInstances (i+1) k
    | LOption.some c => withNewLocalInstance c fvar $ withNewLocalInstances (i+1) k
  else
    k

/--
  `forallTelescopeAux whnf k lctx fvars j type`
  Remarks:
  - `lctx` is the `MetaM` local context exteded with the declaration for `fvars`.
  - `type` is the type we are computing the telescope for. It contains only
    dangling bound variables in the range `[j, fvars.size)`
  - if `reducing? == true` and `type` is not `forallE`, we use `whnf`.
  - when `type` is not a `forallE` nor it can't be reduced to one, we
    excute the continuation `k`.

  Here is an example that demonstrates the `reducing?`.
  Suppose we have
  ```
  abbrev StateM s a := s -> Prod a s
  ```
  Now, assume we are trying to build the telescope for
  ```
  forall (x : Nat), StateM Int Bool
  ```
  if `reducing? == true`, the function executes `k #[(x : Nat) (s : Int)] Bool`.
  if `reducing? == false`, the function executes `k #[(x : Nat)] (StateM Int Bool)`

  if `maxFVars?` is `some max`, then we interrupt the telescope construction
  when `fvars.size == max`
-/
@[specialize] private partial def forallTelescopeReducingAuxAux {α}
    (isClassExpensive : Expr → MetaM (Option Name))
    (reducing?        : Bool) (maxFVars? : Option Nat)
    (k                : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, type@(Expr.forallE n d b c) => do
  let process : Unit → MetaM α := fun _ => do {
    let d     := d.instantiateRevRange j fvars.size fvars;
    fvarId ← mkFreshId;
    let lctx  := lctx.mkLocalDecl fvarId n d c.binderInfo;
    let fvar  := mkFVar fvarId;
    let fvars := fvars.push fvar;
    forallTelescopeReducingAuxAux lctx fvars j b
  };
  match maxFVars? with
  | none          => process ()
  | some maxFVars =>
    if fvars.size < maxFVars then
      process ()
    else
      let type := type.instantiateRevRange j fvars.size fvars;
      adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
        withNewLocalInstances isClassExpensive fvars j $
          k fvars type
| lctx, fvars, j, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstances isClassExpensive fvars j $
      if reducing? then do
        newType ← whnf type;
        if newType.isForall then
          forallTelescopeReducingAuxAux lctx fvars fvars.size newType
        else
          k fvars type
      else
        k fvars type

/- We need this auxiliary definition because it depends on `isClassExpensive`,
   and `isClassExpensive` depends on it. -/
@[specialize] private def forallTelescopeReducingAux {α}
    (isClassExpensive : Expr → MetaM (Option Name))
    (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
newType ← whnf type;
if newType.isForall then do
  lctx ← getLCtx;
  forallTelescopeReducingAuxAux isClassExpensive true maxFVars? k lctx #[] 0 newType
else
  k #[] type

partial def isClassExpensive : Expr → MetaM (Option Name)
| type => withReducible $ -- when testing whether a type is a type class, we only unfold reducible constants.
  forallTelescopeReducingAux isClassExpensive type none $ fun xs type => do
    match type.getAppFn with
    | Expr.const c _ _ => do
      env ← getEnv;
      pure $ if isClass env c then some c else none
    | _ => pure none

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`. -/
def forallTelescope {α} (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
lctx ← getLCtx;
forallTelescopeReducingAuxAux isClassExpensive false none k lctx #[] 0 type

/--
  Similar to `forallTelescope`, but given `type` of the form `forall xs, A`,
  it reduces `A` and continues bulding the telescope if it is a `forall`. -/
def forallTelescopeReducing {α} (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux isClassExpensive type none k

/--
  Similar to `forallTelescopeReducing`, stops constructing the telescope when
  it reaches size `maxFVars`. -/
def forallBoundedTelescope {α} (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux isClassExpensive type maxFVars? k

/-- Return the parameter names for the givel global declaration. -/
def getParamNames (declName : Name) : MetaM (Array Name) := do
cinfo ← getConstInfo declName;
forallTelescopeReducing cinfo.type $ fun xs _ => do
  xs.mapM $ fun x => do
    localDecl ← getLocalDecl x.fvarId!;
    pure localDecl.userName

def isClass (type : Expr) : MetaM (Option Name) := do
c? ← isClassQuick type;
match c? with
| LOption.none   => pure none
| LOption.some c => pure (some c)
| LOption.undef  => isClassExpensive type

/-- Similar to `forallTelescopeAuxAux` but for lambda and let expressions. -/
private partial def lambdaTelescopeAux {α}
    (k : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, Expr.lam n d b c => do
  let d := d.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLocalDecl fvarId n d c.binderInfo;
  let fvar := mkFVar fvarId;
  lambdaTelescopeAux lctx (fvars.push fvar) j b
| lctx, fvars, j, Expr.letE n t v b _ => do
  let t := t.instantiateRevRange j fvars.size fvars;
  let v := v.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLetDecl fvarId n t v;
  let fvar := mkFVar fvarId;
  lambdaTelescopeAux lctx (fvars.push fvar) j b
| lctx, fvars, j, e =>
  let e := e.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstances isClassExpensive fvars j $ do
      k fvars e

/-- Similar to `forallTelescope` but for lambda and let expressions. -/
def lambdaTelescope {α} (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
lctx ← getLCtx;
lambdaTelescopeAux k lctx #[] 0 e

-- `kind` specifies the metavariable kind for metavariables not corresponding to instance implicit `[ ... ]` arguments.
private partial def forallMetaTelescopeReducingAux
    (reducing? : Bool) (maxMVars? : Option Nat) (kind : MetavarKind)
    : Array Expr → Array BinderInfo → Nat → Expr → MetaM (Array Expr × Array BinderInfo × Expr)
| mvars, bis, j, type@(Expr.forallE n d b c) => do
  let process : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    let d  := d.instantiateRevRange j mvars.size mvars;
    let k  := if c.binderInfo.isInstImplicit then  MetavarKind.synthetic else kind;
    mvar ← mkFreshExprMVar d n k;
    let mvars := mvars.push mvar;
    let bis   := bis.push c.binderInfo;
    forallMetaTelescopeReducingAux mvars bis j b
  };
  match maxMVars? with
  | none          => process ()
  | some maxMVars =>
    if mvars.size < maxMVars then
      process ()
    else
      let type := type.instantiateRevRange j mvars.size mvars;
      pure (mvars, bis, type)
| mvars, bis, j, type =>
  let type := type.instantiateRevRange j mvars.size mvars;
  if reducing? then do
    newType ← whnf type;
    if newType.isForall then
      forallMetaTelescopeReducingAux mvars bis mvars.size newType
    else
      pure (mvars, bis, type)
  else
    pure (mvars, bis, type)

/-- Similar to `forallTelescope`, but creates metavariables instead of free variables. -/
def forallMetaTelescope (e : Expr) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
forallMetaTelescopeReducingAux false none kind #[] #[] 0 e

/-- Similar to `forallTelescopeReducing`, but creates metavariables instead of free variables. -/
def forallMetaTelescopeReducing (e : Expr) (maxMVars? : Option Nat := none) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
forallMetaTelescopeReducingAux true maxMVars? kind #[] #[] 0 e

/-- Similar to `forallMetaTelescopeReducingAux` but for lambda expressions. -/
private partial def lambdaMetaTelescopeAux (maxMVars? : Option Nat)
    : Array Expr → Array BinderInfo → Nat → Expr → MetaM (Array Expr × Array BinderInfo × Expr)
| mvars, bis, j, type => do
  let finalize : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    let type := type.instantiateRevRange j mvars.size mvars;
    pure (mvars, bis, type)
  };
  let process : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    match type with
    | Expr.lam n d b c => do
      let d     := d.instantiateRevRange j mvars.size mvars;
      mvar ← mkFreshExprMVar d;
      let mvars := mvars.push mvar;
      let bis   := bis.push c.binderInfo;
      lambdaMetaTelescopeAux mvars bis j b
    | _ => finalize ()
  };
  match maxMVars? with
  | none          => process ()
  | some maxMVars =>
    if mvars.size < maxMVars then
      process ()
    else
      finalize ()

/-- Similar to `forallMetaTelescope` but for lambda expressions. -/
def lambdaMetaTelescope (e : Expr) (maxMVars? : Option Nat := none) : MetaM (Array Expr × Array BinderInfo × Expr) :=
lambdaMetaTelescopeAux maxMVars? #[] #[] 0 e

@[inline] def liftStateMCtx {α} (x : StateM MetavarContext α) : MetaM α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EStateM.Result.ok a { s with mctx := mctx }

def instantiateLevelMVars (lvl : Level) : MetaM Level :=
liftStateMCtx $ MetavarContext.instantiateLevelMVars lvl

def assignLevelMVar (mvarId : MVarId) (lvl : Level) : MetaM Unit :=
modify $ fun s => { s with mctx := MetavarContext.assignLevel s.mctx mvarId lvl }

def mkFreshLevelMVarId : MetaM MVarId := do
mvarId ← mkFreshId;
modify $ fun s => { s with mctx := s.mctx.addLevelMVarDecl mvarId };
pure mvarId

def whnfD : Expr → MetaM Expr :=
fun e => withTransparency TransparencyMode.default $ whnf e

/-- Execute `x` using approximate unification: `foApprox`, `ctxApprox` and `quasiPatternApprox`.  -/
@[inline] def approxDefEq {α} (x : MetaM α) : MetaM α :=
adaptReader (fun (ctx : Context) => { ctx with config := { ctx.config with foApprox := true, ctxApprox := true, quasiPatternApprox := true} })
  x

/--
  Similar to `approxDefEq`, but uses all available approximations.
  We don't use `constApprox` by default at `approxDefEq` because it often produces undesirable solution for monadic code.
  For example, suppose we have `pure (x > 0)` which has type `?m Prop`. We also have the goal `[HasPure ?m]`.
  Now, assume the expected type is `IO Bool`. Then, the unification constraint `?m Prop =?= IO Bool` could be solved
  as `?m := fun _ => IO Bool` using `constApprox`, but this spurious solution would generate a failure when we try to
  solve `[HasPure (fun _ => IO Bool)]` -/
@[inline] def fullApproxDefEq {α} (x : MetaM α) : MetaM α :=
adaptReader (fun (ctx : Context) => { ctx with config := { ctx.config with foApprox := true, ctxApprox := true, quasiPatternApprox := true, constApprox := true } })
  x

@[inline] private def withNewFVar {α} (fvar fvarType : Expr) (k : Expr → MetaM α) : MetaM α := do
c? ← isClass fvarType;
match c? with
| none   => k fvar
| some c => withNewLocalInstance c fvar $ k fvar

def withLocalDecl {α} (n : Name) (type : Expr) (bi : BinderInfo) (k : Expr → MetaM α) : MetaM α := do
fvarId ← mkFreshId;
ctx ← read;
let lctx := ctx.lctx.mkLocalDecl fvarId n type bi;
let fvar := mkFVar fvarId;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
  withNewFVar fvar type k

def withLocalDeclD {α} (n : Name) (type : Expr) (k : Expr → MetaM α) : MetaM α :=
withLocalDecl n type BinderInfo.default k

def withLetDecl {α} (n : Name) (type : Expr) (val : Expr) (k : Expr → MetaM α) : MetaM α := do
fvarId ← mkFreshId;
ctx ← read;
let lctx := ctx.lctx.mkLetDecl fvarId n type val;
let fvar := mkFVar fvarId;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
  withNewFVar fvar type k

/--
  Save cache and `MetavarContext`, bump the `MetavarContext` depth, execute `x`,
  and restore saved data. -/
@[inline] def withNewMCtxDepth {α} (x : MetaM α) : MetaM α := do
s ← get;
let savedMCtx  := s.mctx;
modify $ fun s => { s with mctx := s.mctx.incDepth };
finally x (modify $ fun s => { s with mctx := savedMCtx })

def withLocalContext {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : MetaM α) : MetaM α := do
localInstsCurr ← getLocalInstances;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx, localInstances := localInsts }) $
  if localInsts == localInstsCurr then
    x
  else
    resettingSynthInstanceCache x

/--
  Execute `x` using the given metavariable `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
@[inline] def withMVarContext {α} (mvarId : MVarId) (x : MetaM α) : MetaM α := do
mvarDecl ← getMVarDecl mvarId;
withLocalContext mvarDecl.lctx mvarDecl.localInstances x

@[inline] def withMCtx {α} (mctx : MetavarContext) (x : MetaM α) : MetaM α := do
mctx' ← getMCtx;
modify $ fun s => { s with mctx := mctx };
finally x (modify $ fun s => { s with mctx := mctx' })

/--
  Create an auxiliary definition with the given name, type and value.
  The parameters `type` and `value` may contain free and meta variables.
  A "closure" is computed, and a term of the form `name.{u_1 ... u_n} t_1 ... t_m` is
  returned where `u_i`s are universe parameters and metavariables `type` and `value` depend on,
  and `t_j`s are free and meta variables `type` and `value` depend on. -/
def mkAuxDefinition (name : Name) (type : Expr) (value : Expr) : MetaM Expr := do
env  ← getEnv;
opts ← getOptions;
mctx ← getMCtx;
lctx ← getLCtx;
match Lean.mkAuxDefinition env opts mctx lctx name type value with
| Except.error ex    => throw $ Exception.kernel ex opts
| Except.ok (e, env) => do setEnv env; pure e

/-- Similar to `mkAuxDefinition`, but infers the type of `value`. -/
def mkAuxDefinitionFor (name : Name) (value : Expr) : MetaM Expr := do
type ← inferType value;
let type := type.headBeta;
mkAuxDefinition name type value

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta;
registerTraceClass `Meta.debug

def run {α} (env : Environment) (x : MetaM α) (maxRecDepth := 10000) : Except Exception α :=
match x { maxRecDepth := maxRecDepth, currRecDepth := 0 } { env := env } with
| EStateM.Result.ok a _     => Except.ok a
| EStateM.Result.error ex _ => Except.error ex

end Meta

export Meta (MetaM)

end Lean

open Lean
open Lean.Meta

/-- Helper function for running `MetaM` methods in attributes -/
@[inline] def IO.runMeta {α} (x : MetaM α) (env : Environment) (cfg : Config := {}) (printTraces := true) : IO (α × Environment) :=
match (x { config := cfg, currRecDepth := 0, maxRecDepth := defaultMaxRecDepth }).run { env := env } with
| EStateM.Result.ok a s     => do
  when printTraces $
    s.traceState.traces.forM $ fun msg => IO.println (fmt msg);
  pure (a, s.env)
| EStateM.Result.error ex s => do
  when printTraces $
    s.traceState.traces.forM $ fun msg => IO.println (fmt msg);
  throw (IO.userError (toString ex))
