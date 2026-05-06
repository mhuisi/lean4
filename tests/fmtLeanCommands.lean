import Lean

/-!
Tests for the formatters of the commands, attributes and tactics that `src/Lean` declares outside
of the parser modules: the attribute-set registrations `register_simp_attr`, `register_grind_attr`,
`register_sym_simp_attr` and `register_label_attr`, the deprecated `declare_config_elab_legacy` and
`declare_command_config_elab_legacy` commands (`fmtDeclareConfigElabLegacy`), `register_linter_set`
(`fmtRegisterLinterSet`), the widget commands `#widget` and `show_panel_widgets` together with
their specification parsers (`fmtWidgetCmd`, `fmtShowPanelWidgetsCmd`, `fmtShowWidgetSpec`,
`fmtAddWidgetSpec`, `fmtEraseWidgetSpec`), `test_extern` (`fmtTestExtern`), the
`builtin_env_linter` and `app_delab` attributes (`fmtBuiltinEnvLinter`, `fmtAppDelab`), the trace
commands `postprocess_traces`, `store_traces_as` and `#postprocess_traces` (`fmtTracedCommand`,
`fmtPostprocessStoredTracesCmd`), `reprove` (`fmtReprove`), `aux_def` (`fmtAuxDef`), the
cancellation test syntax of the language server (`fmtWaitForTestTask`, `fmtWaitForSync`,
`fmtBlockUntilCancelled`, `fmtWaitForCancelOnceCommand`) and the `elabToSyntax%` and
`show_term_elab` terms (`fmtElabToSyntax`, `fmtShowTermElabImpl`). Every section contains forms
that fit on one line, forms that exceed the 100 column soft width, and forms with and without each
optional component.

Elaboration of this file fails in many places on purpose: the syntax under test is meant to be used
from within the `Lean` package itself, and only its formatting is of interest here.
-/

open Lean

section AttributeSetRegistrations

register_simp_attr arithNorm

/-- The simp set that normalizes arithmetic goals before they are handed off to `omega`. -/
register_simp_attr omegaPreprocessingLemmasThatAreAppliedBeforeTheGoalIsHandedOffToTheOmegaTactic

register_grind_attr grindArith

/-- The `grind` lemma set describing the shape of the associative containers in `Std.Data`. -/
register_grind_attr grindAssociativeContainerShapeLemmasSharedByHashMapAndTreeMapAndExtTreeMap

register_sym_simp_attr symArith

/-- The symbolic-evaluation simp set used to normalize bitvector expressions before bit blasting. -/
register_sym_simp_attr symBitVecNormalizationLemmasForTheBitBlastingPreprocessorOfBvDecideTactic

register_label_attr extensionality

/-- Declarations tagged with this attribute are tried by the default discharger of `apply_rules`. -/
register_label_attr applyRulesDischargerCandidatesTriedBeforeAssumptionAndReflexivityAndTrivial

end AttributeSetRegistrations

section LegacyConfigElaborators

structure NormNumConfig where
  maxSteps : Nat := 100

declare_config_elab_legacy elabNormNumConfig NormNumConfig

/-- Elaborates the configuration of the `norm_cast` family of tactics. -/
declare_config_elab_legacy elabNormCastConfigurationForTheTacticFrontend NormCastTacticElaborationConfig

declare_command_config_elab_legacy elabGuardMsgsConfig GuardMsgsConfig

/-- Elaborates the configuration of the `#print axioms` command. -/
declare_command_config_elab_legacy elabPrintAxiomsCommandConfiguration PrintAxiomsCommandConfiguration

end LegacyConfigElaborators

section LinterSets

register_linter_set emptyLinterSet :=

register_linter_set styleLinters := unusedVariables

/-- Every linter that reports a stylistic issue rather than a likely mistake. -/
register_linter_set mathlibStyleLinters := unusedVariables deprecated missingDocs

register_linter_set allDefaultLinters := unusedVariables deprecated unnecessarySimpa
  suspiciousUnexpanderPatterns constructorNameAsVariable unusedSectionVars missingDocs
  missingFormatter

end LinterSets

section Widgets

#widget goalStatePanel

#widget selectionPanel with Json.mkObj [("goal", "⊢ ∀ n, n + 0 = n")]

#widget interactiveDiagnosticsPanelForTheInfoView with
  Json.mkObj [("kind", "diagnostics"), ("severity", "warning"), ("range", Json.null)]

show_panel_widgets [goalStatePanel]

show_panel_widgets [-goalStatePanel]

show_panel_widgets [local selectionPanel with Json.mkObj [("selected", true)]]

show_panel_widgets [scoped goalStatePanel, local selectionPanel, -interactiveDiagnosticsPanel]

show_panel_widgets [goalStatePanel with Json.mkObj [("collapsed", false)], -legacyGoalStatePanel,
  scoped interactiveDiagnosticsPanelForTheInfoView with Json.mkObj [("severity", "error")]]

end Widgets

section TestExtern

test_extern Nat.add 2 3

test_extern String.append "the first of two rather long string literals, joined by " "String.append!"

end TestExtern

section Attributes

@[builtin_env_linter linter.envLinter.unusedArguments]
def unusedArgumentsEnvLinter : Linter.EnvLinter.EnvLinter where
  test := fun _ => return none
  noErrorsFound := "no unused arguments found"
  errorsFound := "found unused arguments"

@[builtin_env_linter linter.envLinter.simpVarHeadThatIsCheckedForEverySimpLemmaInTheWholeEnvironment]
def simpVarHeadEnvLinter : Linter.EnvLinter.EnvLinter where
  test := fun _ => return none
  noErrorsFound := "no malformed simp lemmas found"
  errorsFound := "found malformed simp lemmas"

@[app_delab Nat.succ]
def delabNatSucc : PrettyPrinter.Delaborator.Delab := failure

@[app_delab Std.Tactic.BVDecide.BVExpr.bitblast.instLawfulVecOperatorShiftTargetBlastArithShiftRightConst]
def delabLawfulArithShiftRightConst : PrettyPrinter.Delaborator.Delab := failure

end Attributes

section Traces

open Lean.PostprocessTraces

set_option trace.Meta.synthInstance true in
postprocess_traces filterSubtrees (containsString "tryResolve") in
example : Inhabited (List Nat) := inferInstance

postprocess_traces filterSubtrees (containsString "tryResolve") >=> hoist (ofClass `Meta) in
example : Inhabited (List Nat) := inferInstance

store_traces_as instanceSynthesis in
example : Inhabited (List Nat) := inferInstance

store_traces_as theInstanceSynthesisOfAVeryDeeplyNestedInhabitedInstanceForNestedLists in
example : Inhabited (List (List (List Nat))) := inferInstance

#postprocess_traces instanceSynthesis selfTime

#postprocess_traces instanceSynthesis filterSubtrees (minTimeMs 10) >=> exposeSubtrees (ofClass `Meta)

end Traces

section Reprove

theorem addZero (n : Nat) : n + 0 = n := by simp

theorem addComm (n m : Nat) : n + m = m + n := by omega

reprove addZero by simp

reprove addZero addComm by simp

reprove addZero addComm List.append_nil List.length_append List.getElem_append Array.size_push
  Array.size_set Array.getElem_push_lt List.map_append List.filter_append by
  simp

reprove addComm by
  intro n m
  omega

end Reprove

section AuxDefs

open Lean.Elab.Command in
private aux_def answer : Nat := 42

open Lean.Elab.Command in
/-- The auxiliary definition backing the `elab_rules` expansion for a command elaborator. -/
@[inline] public aux_def elabRules commandElab : Nat := 0

open Lean.Elab.Command in
private aux_def theAuxiliaryDefinitionOfAnElaboratorWithAVeryLongSuggestedNameThatMustBreak :
    List (Nat × String) := [(1, "one"), (2, "two")]

end AuxDefs

section ServerCancellationTests

open Lean.Server.Test.Cancel

-- Outside the language server the cancellation token is never set, so these would block forever.
elab_rules : command
  | `(command| wait_for_cancel_once_command $_n) => pure ()

elab_rules : tactic
  | `(tactic| wait_for_sync $_label) => pure ()
  | `(tactic| block_until_cancelled $_label) => pure ()

wait_for_cancel_once_command 0

wait_for_cancel_once_command 1234567890123456789012345678901234567890123456789012345678901234567890

example : True := by
  wait_for_test_task "backgroundRequest"
  trivial

example : True := by
  wait_for_sync "theSynchronizationPointBetweenTheRequestHandlerAndTheDocumentElaborationTaskOfTheFileWorker"
  block_until_cancelled "theFirstElaborationOfTheTheoremThatIsCancelledByTheFollowingEditOfTheUser"
  trivial

end ServerCancellationTests

section FixedTermElaborators

def fixedElaboratorReference : Nat := elabToSyntax% 0

def fixedElaboratorReferenceWithALongNameSoThatTheApplicationHasToBreakAcrossLines : Nat :=
  elabToSyntax% 17

def shownTerm : Nat := show_term_elab 1 + 1

def shownTermThatDoesNotFitOnASingleLineTogetherWithItsRatherLongDeclarationName : List Nat :=
  show_term_elab List.range 10 |>.filter (· % 2 == 0) |>.map (· * 3) |>.reverse

end FixedTermElaborators
