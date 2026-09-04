import Lean

/-!
Tests that `linter.fmt.missing` resolves ambiguous `choice` nodes through the info trees of
the command it lints.

The linter used to pass no resolution to the formatter at all, so every `choice` node whose
alternatives render differently fell back to the source text without a word. Now the linter finds
the `ChoiceResolutionInfo` that the elaborator recorded, and reports the node only when there is
no such resolution.
-/

open Lean Lean.Fmt

-- Two term syntaxes that accept the same input, so the parser produces a `choice` node.
syntax (name := choiceA) "choiceTest " term : term
syntax (name := choiceB) "choiceTest " term : term

open Lean Elab Term in
@[term_elab choiceA] def elabChoiceA : TermElab := fun stx _ => elabTerm stx[1] none

open Lean Elab Term in
@[term_elab choiceB] def elabChoiceB : TermElab := fun _ _ => throwError "choiceB failed"

/-- Drops the leading token, so the document differs from the one `fmtChoiceB` produces.
`fmtChoiceNode` only asks for a resolution when the alternatives disagree. -/
@[fmt choiceA]
def fmtChoiceA : Fmt := fun stx => fmt stx[1]

@[fmt choiceB]
def fmtChoiceB : Fmt := fmtAtomic

set_option linter.fmt.missing true

-- `choiceB` fails to elaborate, so the elaborator commits to `choiceA` and records the choice.

#guard_msgs in
example : Nat := choiceTest 1

-- Both alternatives fail to elaborate, so nothing records a resolution and the linter says so.

syntax (name := choiceC) "choiceFail " term : term
syntax (name := choiceD) "choiceFail " term : term

open Lean Elab Term in
@[term_elab choiceC] def elabChoiceC : TermElab := fun _ _ => throwError "choiceC failed"

open Lean Elab Term in
@[term_elab choiceD] def elabChoiceD : TermElab := fun _ _ => throwError "choiceD failed"

@[fmt choiceC]
def fmtChoiceC : Fmt := fun stx => fmt stx[1]

@[fmt choiceD]
def fmtChoiceD : Fmt := fmtAtomic

/--
error: overloaded, errors 
  choiceD failed
  
  choiceC failed
---
warning: The auto-formatter failed, so this command was not checked for missing formatters:

A choice node was not disambiguated by the elaborator:
(choice (choiceD "choiceFail" (num "1")) (choiceC "choiceFail" (num "1")))

Note: This linter can be disabled with `set_option linter.fmt.missing false`
-/
#guard_msgs in
example : Nat := choiceFail 1
