import Lean

/-!
Tests for the formatters of syntax that is defined in `src/Lean` itself: the `m!` message
interpolation (`fmtMessageDataInterpolation`), the trace and issue-reporting instructions
`trace[...]`, `trace_goal[...]`, `reportIssue!`, `reportDbgIssue!` and `reportEMatchIssue!`
(`fmtTraceTerm` and friends), the option registrations `register_builtin_option` and
`register_option` (`fmtOptionRegistration`), `register_parser_alias`
(`fmtRegisterParserAlias`), the `Lean.Elab.ConfigEval` commands (`fmtEnsureEvalInstance`,
`fmtDefEvalConfigItemCmd`, `fmtDeclareConfig`, `fmtWithConfigEntries` and the `where`-clause
entries), the ground-evaluation and simproc-declaration macros `declare_eval_bin`,
`declare_eval_bin_bitwise`, `declare_eval_bin_bool_pred`, `declare_uint_simprocs`,
`declare_sint_simprocs` and `elab_stx_quot`, and the `json%` notation (`fmtJsonTerm`,
`fmtJsonObject`, `fmtJsonField`, `fmtJsonIdent`, `fmtJsonArray`, `fmtJsonNum`,
`fmtJsonScientific`, `fmtJsonStr`) together with `fmtScientific`. Every section contains forms
that fit on one line, forms that exceed the 100 column soft width, and forms with and without
each optional component.

Elaboration of this file fails in several places on purpose: the commands under test are meant
to be used from within the `Lean` package itself, and only their formatting is of interest here.
-/

open Lean

section MessageInterpolation

example : MessageData := m!"nothing to interpolate here"

example (declName : Name) : MessageData := m!"failed to synthesize `{declName}`"

example (e : Expr) : MessageData :=
  m!"found term that has not been internalized{indentExpr e}"

example (e type : Expr) : MessageData :=
  m!"failed to apply the extensionality theorem to {indentExpr e}\nbecause it is not definitionally equal to{indentExpr type}"

example (thmName : Name) (lhs rhs : Expr) : MessageData :=
  m!"invalid generalized pattern at `{thmName}`\nfailed to prove{indentExpr lhs}\nis equal to{indentExpr rhs}"

end MessageInterpolation

section Trace

def traceWithoutInterpolation : CoreM Unit := do
  trace[Elab.step] "entering the elaborator"

def traceWithInterpolation (declName : Name) : CoreM Unit := do
  trace[Meta.synthInstance] "synthesized an instance for `{declName}`"

def traceWithLongMessage (e type : Expr) : CoreM Unit := do
  trace[Meta.isDefEq] "failed to unify the two sides of the equation{indentExpr e}\nagainst the expected type{indentExpr type}"

def traceWithLongTraceClass (e : Expr) : CoreM Unit := do
  trace[Meta.Tactic.simp.rewrite.discharge] "discharging the side condition{indentExpr e}"

def traceWithTermMessage (msg : MessageData) : CoreM Unit := do
  trace[Elab.command] msg

def traceWithComputedTermMessage (goals : List MVarId) : CoreM Unit := do
  trace[Elab.command] (MessageData.joinSep (goals.map (m!"{·}")) ", ")

end Trace

section GrindAndSymTracing

open Lean.Meta.Grind Lean.Meta.Sym

def traceGoalShort : GoalM Unit := do
  trace_goal[grind.debug] "starting a new round"

def traceGoalLong (e : Expr) : GoalM Unit := do
  trace_goal[grind.debug.proofs] "constructed a proof for the equality{indentExpr e}\nusing congruence closure"

def traceGoalTerm (msg : MessageData) : GoalM Unit := do
  trace_goal[grind.debug] msg

def reportSymIssues (e type : Expr) : SymM Unit := do
  reportIssue! "unsupported term{indentExpr e}"
  reportIssue! "expression{indentExpr e}\nhas an unexpected type{indentExpr type}, so it cannot be normalized"
  reportDbgIssue! "cache miss"
  reportDbgIssue! "the normalizer produced a term{indentExpr e}\nthat is not structurally smaller than its input"
  reportEMatchIssue! "unexpected number of parameters"
  reportEMatchIssue! "failed to instantiate the theorem because its proposition{indentExpr type}\ncontains universe metavariables"

def reportTermIssue (msg : MessageData) : SymM Unit := do
  reportIssue! msg
  reportDbgIssue! msg
  reportEMatchIssue! msg

end GrindAndSymTracing

section OptionRegistrations

register_builtin_option fmtTest.enabled : Bool := {
  defValue := true
  descr := "enable the feature"
}

/-- Controls how many rewrite steps the normalizer is allowed to take. -/
register_builtin_option fmtTest.maxRewriteSteps : Nat := { defValue := 1000, descr := "maximum number of rewrite steps" }

public register_builtin_option fmtTest.veryLongOptionName.experimentalNormalizationStrategy : String := {
  defValue := "default"
  descr := "selects the normalization strategy used by the experimental code path"
}

register_option fmtTest.verbose : Bool := { defValue := false, descr := "print progress information" }

/-- Threshold above which the solver gives up. -/
private register_option fmtTest.threshold : Nat := {
  defValue := 42
  descr := "give up once the search tree exceeds this many nodes"
}

end OptionRegistrations

section ParserAliases

open Lean.Parser

initialize
  register_parser_alias many
  register_parser_alias "ws" checkWsBefore { stackSz? := some 0 }
  register_parser_alias (kind := numLitKind) "num" numLit
  register_parser_alias (kind := identKind) ident
  register_parser_alias (kind := ``Lean.Parser.Term.optType) "optionalTypeAscriptionWithAVeryLongAliasName" Lean.Parser.Term.optType { autoGroupArgs := false, stackSz? := some 1 }

end ParserAliases

section ConfigEval

open Lean.Elab Lean.Elab.ConfigEval

structure FmtTestConfig where
  verbose : Bool := false
  maxSteps : Nat := 100
  strategy : String := "default"

ensure_eval_term_instance FmtTestConfig

private local ensure_eval_expr_instance FmtTestConfig

scoped ensure_eval_term_expr_instances Lean.Elab.Tactic.FmtTestNamespaceWithAVeryLongName.FmtTestConfig

private local derive_eval_expr_instance_using_meta_eval FmtTestConfig

def_eval_config_item FmtTestConfigItem for FmtTestConfig

/-- The configuration item structure used by the `fmt_test` tactic. -/
private def_eval_config_item FmtTestConfigItemWithBinders (evalStrategy : Syntax → TermElabM String) [Inhabited FmtTestConfig] for FmtTestConfig where
  omit strategy
  option strategy := fun cfg item => do
    let strategy ← evalStrategy item.value
    return { cfg with strategy }

declare_config_elab elabFmtTestConfig FmtTestConfig

private declare_core_config_elab elabFmtTestCoreConfig FmtTestConfig where
  omit verbose

declare_term_config_elab elabFmtTestTermConfig FmtTestConfig (evalConfig : Syntax → TermElabM FmtTestConfig) where
  option verbose := fun cfg _ => return { cfg with verbose := true }

/-- Elaborates the configuration of the `#fmt_test` command. -/
private declare_command_config_elab elabFmtTestCommandConfig FmtTestConfig where
  omit verbose, maxSteps, strategy
  option verbose := fun cfg _ => return { cfg with verbose := true }
  option strategy.* := fun cfg _ => return { cfg with strategy := "custom" }
  option * := fun _ item => do
    throwErrorAt item.root "Unsupported configuration option for the `#fmt_test` command, use `verbose` or `strategy.*` instead"

declare_config_elab elabFmtTestConfigWithLongBinders FmtTestConfig (evalConfig : Syntax → TermElabM FmtTestConfig) (evalStrategy : Syntax → TermElabM String) where
  omit strategy

declare_command_config_elab elabFmtTestCommandConfigWithAnExtremelyLongNameThatDoesNotFit FmtTestConfig

structure FmtTestWideConfig where
  verbose : Bool := false
  maxSteps : Nat := 100
  normalizationStrategy : String := "default"
  useInstantiationCache : Bool := true
  reportProgressAfterEveryStep : Bool := false
  failOnFirstNormalizationError : Bool := true
  emitDiagnosticsForEveryRewriteStep : Bool := false

declare_config_elab elabFmtTestWideConfig FmtTestWideConfig where
  omit verbose, maxSteps, normalizationStrategy, useInstantiationCache, reportProgressAfterEveryStep, failOnFirstNormalizationError, emitDiagnosticsForEveryRewriteStep
  option experimental.normalization.strategy := fun cfg _ =>
    return { cfg with normalizationStrategy := "experimental" }

private def_eval_config_item FmtTestWideConfigItemWithAnExtremelyLongName [Inhabited FmtTestWideConfig] for FmtTestWideConfig where
  omit verbose, maxSteps
  option experimental.* := fun cfg _ => return cfg

end ConfigEval

section GroundEvaluation

open Lean.Meta.Sym.DSimp

declare_eval_bin evalAddOfSomeSort (· + ·)

declare_eval_bin evalMulWithAnExtremelyLongDeclarationNameThatDoesNotFit (fun a b => a * b + a)

declare_eval_bin_bitwise evalAnd (· &&& ·)

declare_eval_bin_bitwise evalShiftLeftWithAnExtremelyLongDeclarationName (fun a b => a <<< (b % 64))

declare_eval_bin_bool_pred evalBEq (· == ·)

declare_eval_bin_bool_pred evalLessThanOrEqualWithAnExtremelyLongDeclarationName (fun a b => a ≤ b)

end GroundEvaluation

section SimprocDeclarations

declare_uint_simprocs UInt8

declare_uint_simprocs UInt64

declare_sint_simprocs Int8

declare_sint_simprocs Int64

elab_stx_quot Parser.Term.quot

elab_stx_quot Lean.Parser.Term.dynamicQuotWithAnExtremelyLongParserNameThatDoesNotFitOnOneLine

end SimprocDeclarations

section Json

open Lean.Json

def jsonNullLiteral : Json := json% null

def jsonTrueLiteral : Json := json% true

def jsonStringLiteral : Json := json% "a plain string"

def jsonNumberLiteral : Json := json% 100

def jsonNegativeNumberLiteral : Json := json% -100

def jsonScientificLiteral : Json := json% 100.5e30

def jsonNegativeScientificLiteral : Json := json% -100.5e30

def jsonEmptyObject : Json := json% {}

def jsonSmallObject : Json := json% { hello : "world" }

def jsonSmallArray : Json := json% ["edam", "cheddar"]

def jsonNestedObject : Json := json%
  { name : "cheese", "quoted key" : -1, rank : 100.2, spicy : false, tags : ["edam", "cheddar"] }

def jsonLongObject : Json := json% { name : "a rather long name for a cheese", origin : "the Netherlands", rank : -100.25e10, isSpicy : false, isAvailable : null }

def jsonDeeplyNested : Json := json%
  { hello : "world",
    cheese : ["edam", "cheddar", { kind : "spicy", rank : 100.2, origin : { country : "France", region : "Normandy" } }],
    lemonCount : 100e30,
    isCool : true,
    isBug : null }

def jsonArrayOfObjects : Json := json%
  [{ id : 1, label : "first" }, { id : 2, label : "second" }, { id : 3, label : "third" }, { id : 4, label : "fourth" }]

def jsonWithAntiquotation (n : Nat) : Json := json% { computed : $(23 + 54 * 2), given : $n }

def jsonWithAntiquotationSplice (xs : Array Json) (v : Json) : Json := json% [$[$xs],*, $v]

end Json

section Scientific

example : Float := 1.5

example : Float := 100.5e30

example : Float := 0.000001

end Scientific
