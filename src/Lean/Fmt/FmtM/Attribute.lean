/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.KeyedDeclsAttribute
public import Lean.Util.ShareCommon
public import Lean.Fmt.FmtM.LineInfo
import Lean.Compiler.InitAttr
import Lean.ExtraModUses
import Lean.Fmt.Util.Module
public import Lean.Fmt.Core.Formatter
public import Lean.Language.Lean.Types

namespace Lean.Fmt

/--
Cost type used for the documents produced by `FmtM` formatters: the default cost function with a
page width limit of 100 and an optimality cutoff width of 200.
-/
public abbrev FmtCost := DefaultCost 100 200

public structure FormattedWhitespace where
  formattedLeadingRanges : Array Syntax.Range
  formattedTrailingRanges : Array Syntax.Range
  deriving Repr

public structure MissingFormatter where
  kind : SyntaxNodeKind

public structure PartialFormatter where
  stx : Syntax
  formatterName : Name

public structure Context where
  env : Environment
  text : FileMap
  initialSnap? : Option Language.Lean.InitialSnapshot
  opts : Options
  lineInfos : Array SyntaxLineInfo

public inductive RangeKind where
  | whitespace
  | node
  | text
  deriving Inhabited

public structure BacktrackableState where
  tags : Std.HashMap Syntax.Range (Array TagId × RangeKind)
  deriving Inhabited

public structure State extends BacktrackableState where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  missingFormatters : Std.HashMap Syntax.Range MissingFormatter
  partialFormatters : Std.HashMap Syntax.Range PartialFormatter
  deriving Inhabited

public instance : EStateM.Backtrackable BacktrackableState State where
  save s := s.toBacktrackableState
  restore s d := { s with toBacktrackableState := d }

public structure TaggedDoc.MetaData where
  v : Dynamic
  propagate : Dynamic → (Doc FmtCost → Doc FmtCost) → Dynamic

public structure TaggedDoc where
  doc : Doc FmtCost
  metaData : List TaggedDoc.MetaData := []
  deriving Inhabited

end Lean.Fmt

namespace Lean

public abbrev FmtM α := ReaderT Fmt.Context (EStateM Fmt.Error Fmt.State) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

end Lean

namespace Lean.Fmt

/--
Determines the formatter to use for a syntax node kind, together with the name of the declaration
it originates from (which is reported when the formatter turns out to be incomplete).
Yields `none` if the provider is not responsible for the kind.
-/
public abbrev FmtProvider := Environment → Options → SyntaxNodeKind → Option (Name × Fmt)

public structure FmtProviderEntry where
  priority : Nat
  provider : FmtProvider

/-- The list of builtin `FmtProvider`s, ordered by decreasing priority. -/
builtin_initialize builtinFmtProvidersRef : IO.Ref (Array FmtProviderEntry) ← IO.mkRef #[]

/--
Adds a new builtin `FmtProvider`. Providers are consulted in order of decreasing priority and the
first provider that is responsible for a syntax node kind determines its formatter. Providers of
equal priority are consulted in the order in which they were added. The priorities used by core are:
* 1100 for choice nodes,
* 1000 for the formatters registered with `@[{builtin_}fmt]`,
* 900 for antiquotations,
* 800 for the formatters registered with a specialized attribute
  (`@[{builtin_}infix_fmt]`, `@[{builtin_}conditional_fmt]`, `@[{builtin_}quantifier_fmt]`),
* 600 for the operator formatters derived from the `ParserDescr` of a notation,
* 400 for the atomic formatter derived from the `ParserDescr` of syntax that only parses atoms.

This function should only be used from within the `Lean` package.
-/
public def addBuiltinFmtProvider (priority : Nat) (provider : FmtProvider) : IO Unit :=
  builtinFmtProvidersRef.modify fun providers =>
    let i := providers.findIdx? (·.priority < priority) |>.getD providers.size
    providers.insertIdx! i { priority, provider }

builtin_initialize fmtProvidersExt : EnvExtension (Array FmtProviderEntry) ←
  registerEnvExtension builtinFmtProvidersRef.get

/-- The registered `FmtProvider`s, ordered by decreasing priority. -/
public def getFmtProviders (env : Environment) : Array FmtProviderEntry :=
  fmtProvidersExt.getState env

/--
The `FmtProvider` of an attribute that registers formatters keyed by syntax node kind, where `mk`
turns a registered value into the formatter it stands for.
-/
public def keyedFmtProvider {α : Type} (attr : KeyedDeclsAttribute α) (mk : α → Fmt) : FmtProvider :=
  fun env _ kind => do
    let entry ← attr.getEntries env kind |>.head?
    return (entry.declName, mk entry.value)

/-- Elaborates the syntax node kind argument of an attribute that registers a formatter. -/
private def evalFmtAttributeKey (attrName : Name) (extraKinds : List SyntaxNodeKind := [])
    (builtin : Bool) (stx : Syntax) : AttrM Name := do
  let env ← getEnv
  let stx ← Attribute.Builtin.getIdent stx
  let id := stx.getId
  -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
  -- synthesize a formatter for it immediately, so we just check for a declaration in this case
  if ! (builtin && (env.find? id).isSome || Parser.isValidSyntaxNodeKind env id || extraKinds.contains id) then
    throwError "Invalid `[{attrName}]` argument: Unknown syntax kind `{id}`"
  if (← getEnv).contains id then
    recordExtraModUseFromDecl (isMeta := false) id
    if (← Elab.getInfoState).enabled then
      Elab.addConstInfo stx id none
  pure id

public unsafe builtin_initialize fmtAttribute : KeyedDeclsAttribute Fmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_fmt,
    name := `fmt,
    descr := "Register an Fmt formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt,
    evalKey := evalFmtAttributeKey `fmt [moduleKind, cmdsKind, headerKind]
  }

/--
Determines whether the given term, when it occurs as an argument of an application,
propagates the stickiness of its right-hand side to the full application.
-/
public abbrev StickyTermFn := TSyntax `term → Bool

/-- Interpret a `StickyTermFn` from the environment. -/
def mkStickyTermFn (constName : Name) : ImportM StickyTermFn := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck StickyTermFn opts ``StickyTermFn constName

/-- The list of builtin `StickyTermFn`s. -/
builtin_initialize builtinStickyTermFnsRef : IO.Ref (Array StickyTermFn) ← IO.mkRef #[]

/-- Adds a new builtin `StickyTermFn`.
This function should only be used from within the `Lean` package. -/
public def addBuiltinStickyTermFn (f : StickyTermFn) : IO Unit :=
  builtinStickyTermFnsRef.modify (·.push f)

/-- An extension which keeps track of registered `StickyTermFn`s. -/
builtin_initialize stickyTermFnsExt :
    PersistentEnvExtension Name (Name × StickyTermFn) (Array Name × Array StickyTermFn) ←
  registerPersistentEnvExtension {
    mkInitial       := return (#[], ← builtinStickyTermFnsRef.get)
    addImportedFn   := fun as => do
      (#[], ·) <$> as.foldlM (init := ← builtinStickyTermFnsRef.get) fun s as =>
        as.foldlM (init := s) fun s n => s.push <$> mkStickyTermFn n
    addEntryFn      := fun (names, fns) (n, f) => (names.push n, fns.push f)
    exportEntriesFn := (·.1)
  }

/-- Adds the `@[{builtin_}fmt_sticky_term]` attribute, which is applied to declarations of type
`StickyTermFn` for use in the formatting of applications. -/
builtin_initialize
  let mkAttr (builtin : Bool) (name : Name) := registerBuiltinAttribute {
    name
    descr := (if builtin then "(builtin) " else "") ++
      "Marks a function of type `Lean.Fmt.StickyTermFn` that determines whether a term \
       propagates the stickiness of its right-hand side in applications."
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      if !builtin then
        ensureAttrDeclIsMeta name decl kind
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      let declType := (← getConstInfo decl).type
      unless declType.isConstOf ``StickyTermFn do
        throwAttrDeclNotOfExpectedType name decl declType (mkConst ``StickyTermFn)
      if builtin then
        declareBuiltin decl <| mkApp (mkConst ``addBuiltinStickyTermFn) (mkConst decl)
      else
        setEnv <| stickyTermFnsExt.addEntry (← getEnv) (decl, ← mkStickyTermFn decl)
  }
  mkAttr true `builtin_fmt_sticky_term
  mkAttr false `fmt_sticky_term

/--
Returns `true` if any function registered with the `@[{builtin_}fmt_sticky_term]` attribute
determines that `t` propagates the stickiness of its right-hand side.
-/
public def propagatesRhsStickiness (env : Environment) (t : TSyntax `term) : Bool :=
  (stickyTermFnsExt.getState env).2.any (· t)

public inductive InfixOperationAssociativity where
  | left
  | right
  | middle
  deriving BEq

/-- The infix operation that a syntax node kind denotes. -/
public structure InfixOperation where
  assoc : InfixOperationAssociativity
  /--
  Further syntax node kinds that an operator chain containing this operator may continue with,
  for operators that are spread over several syntax node kinds (such as `→` and its dependent
  variant).
  -/
  extendedChainKinds : Array SyntaxNodeKind := #[]

public unsafe builtin_initialize infixFmtAttribute : KeyedDeclsAttribute InfixOperation ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_infix_fmt,
    name := `infix_fmt,
    descr := "Register an Fmt infix operation formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt.InfixOperation,
    evalKey := evalFmtAttributeKey `infix_fmt
  }

public structure Conditional.ElseIf where
  elseTk : Syntax
  ifTk : Syntax
  cond : TaggedDoc
  thenTk : Syntax
  body : Syntax

public structure Conditional where
  ifTk : Syntax
  cond : TaggedDoc
  thenTk : Syntax
  thenBody : Syntax
  elseIfs : Array Conditional.ElseIf := #[]
  elseTk? : Option Syntax
  elseBody? : Option Syntax

public abbrev ConditionalFmt := Syntax → FmtM (Option Conditional)

public unsafe builtin_initialize conditionalFmtAttribute : KeyedDeclsAttribute ConditionalFmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_conditional_fmt,
    name := `conditional_fmt,
    descr := "Register an Fmt conditional formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt.ConditionalFmt,
    evalKey := evalFmtAttributeKey `conditional_fmt
  }

/-- Binders partitioned into layout groups, as produced by `groupBinders`. -/
public abbrev BinderGroups := Array (Array Syntax)

public inductive QuantifierBinders where
  | binders (group : BinderGroups)
  | pred (lhs : Syntax) (rhs : TSyntax `binderPred)

public structure QuantifierHeadComponents where
  quantifier : Syntax
  binders : QuantifierBinders
  typeAscriptionTk? : Option Syntax
  type? : Option Syntax
  commaTk : Syntax

public structure QuantifierComponents extends QuantifierHeadComponents where
  body : Syntax

public abbrev QuantifierFmt := Syntax → Option QuantifierComponents

public unsafe builtin_initialize quantifierFmtAttribute : KeyedDeclsAttribute QuantifierFmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_quantifier_fmt,
    name := `quantifier_fmt,
    descr := "Register an Fmt quantifier formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt.QuantifierFmt,
    evalKey := evalFmtAttributeKey `quantifier_fmt
  }
