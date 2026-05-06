import Lean

/-!
Tests for the simproc-family formatters (`fmtSimprocLike`, `fmtSimprocPatternLike`,
`fmtSimprocAttrLike`): the `simproc`, `dsimproc` and `cbv_simproc` commands together with their
`builtin_` and `_decl` variants, the `simproc_pattern%` commands, and the simproc attributes.
The examples exercise the optional phase modifier (`↓`/`↑`/`cbv_eval`), the optional `[...]`
list of simproc sets, doc comments and attribute kinds, and triggers, names and bodies of
varying length so that the layout has to break in different places.
-/

open Lean Meta Simp

namespace SimprocTests

theorem and_false_eq {p : Prop} (q : Prop) (h : p = False) : (p ∧ q) = False := by simp [*]

section Simproc

simproc shortCircuitAnd (And _ _) := fun e => do
  let_expr And p q := e | return .continue
  let r ← simp p
  let_expr False := r.expr | return .continue
  let proof ← mkAppM ``and_false_eq #[q, (← r.getProof)]
  return .done { expr := r.expr, proof? := some proof }

simproc ↓ preNormalizeAnd (And _ _) := fun _ => return .continue

simproc ↑ postNormalizeOr (Or _ _) := fun _ => return .continue

simproc [simp] reduceIdentityFunction (id _) := fun _ => return .continue

simproc ↓ [simp, seval] reduceNestedIte (ite _ (ite _ _ _) _) := fun _ => return .continue

scoped simproc [simp] scopedReduceListAppend (List.append _ _) := fun _ => return .continue

local simproc ↑ [seval] localReduceArraySize (Array.size _) := fun _ => return .continue

/--
Rewrites `n + 0` to `n`, and is registered in both the `simp` and the symbolic evaluation
simproc sets so that it also fires during `seval`.
-/
simproc ↓ [simp, seval] reduceAddZeroOnNaturalNumbers (HAdd.hAdd (_ : Nat) (0 : Nat)) :=
  fun _ => return .continue

simproc aVeryLongSimprocNameThatBarelyFitsOnASingleLine (HMul.hMul (Nat.succ _) (Nat.succ _)) :=
  fun _ => return .continue

simproc ↓ [simp, seval] normalizeDeeplyNestedArithmeticExpression
    (HAdd.hAdd (HMul.hMul (_ : Nat) (_ : Nat)) (HMul.hMul (_ : Nat) (_ : Nat))) :=
  fun e => do
    let_expr HAdd.hAdd _ _ _ _ lhs rhs := e | return .continue
    let lhs ← simp lhs
    let rhs ← simp rhs
    return .visit { expr := mkNatAdd lhs.expr rhs.expr }

simproc [simp, seval, arith, ground, propositionalSimplification] setListIsLongEnoughToBreak
    (Nat.ble _ _) := fun _ => return .continue

end Simproc

section DSimproc

dsimproc dropUnitArgument (PUnit.unit) := fun _ => return .continue

dsimproc ↓ [simp] unfoldDefinitionalEqualityForProjections (Prod.fst (Prod.mk _ _)) :=
  fun _ => return .continue

/-- Definitionally reduces `Nat.succ n - 1` to `n`. -/
scoped dsimproc ↑ [seval] reduceSuccPredOnNaturalNumbers (HSub.hSub (Nat.succ _) (1 : Nat)) :=
  fun _ => return .continue

end DSimproc

section Decls

simproc_decl inactiveShortCircuitAnd (And _ _) := fun _ => return .continue

/-- A declaration that is only activated by an explicit `attribute [simproc]` command. -/
simproc_decl reduceApplicationOfAVeryLongIdentifierName (Nat.rec _ _ _) :=
  fun e => do
    let_expr Nat.rec _ z s := e | return .continue
    return .done { expr := mkApp2 (mkConst ``Nat.recAux) z s }

dsimproc_decl inactiveDropUnitArgument (PUnit.unit) := fun _ => return .continue

dsimproc_decl reduceDefinitionalProjectionOfAnExplicitlyConstructedPair (Prod.snd (Prod.mk _ _)) :=
  fun _ => return .continue

end Decls

section Builtin

builtin_simproc builtinReduceNatAdd (HAdd.hAdd _ _) := fun _ => return .continue

builtin_simproc ↓ [seval] builtinPreReduceNatMul (HMul.hMul _ _) := fun _ => return .continue

builtin_simproc ↑ [simp, seval] builtinPostNormalizeBitVectorConcatenation (BitVec.append _ _) :=
  fun _ => return .continue

builtin_dsimproc builtinDropDecidableInstance (Decidable.decide _) := fun _ => return .continue

builtin_dsimproc ↓ [simp, seval] builtinReduceDefinitionalMatchOnConstructor (Nat.rec _ _ _) :=
  fun _ => return .continue

builtin_simproc_decl builtinInactiveReduceNatSub (HSub.hSub _ _) := fun _ => return .continue

/-- A builtin declaration whose body needs several lines. -/
builtin_simproc_decl builtinReduceStringAppendOnLiteralArguments (HAppend.hAppend _ _) :=
  fun e => do
    let_expr HAppend.hAppend _ _ _ _ lhs rhs := e | return .continue
    let some lhs := lhs.rawNatLit? | return .continue
    let some rhs := rhs.rawNatLit? | return .continue
    return .done { expr := mkRawNatLit (lhs + rhs) }

builtin_dsimproc_decl builtinInactiveDropUnitArgument (PUnit.unit) := fun _ => return .continue

builtin_dsimproc_decl builtinReduceIdentityCoercionBetweenIntegerTypes (Int.toNat (Int.ofNat _)) :=
  fun _ => return .continue

end Builtin

section CbvSimproc

cbv_simproc cbvReduceIdentityFunction (id _) := fun _ => return .continue

cbv_simproc ↓ cbvPreReduceListLength (List.length _) := fun _ => return .continue

cbv_simproc ↑ cbvPostReduceArraySize (Array.size _) := fun _ => return .continue

cbv_simproc cbv_eval cbvEvalReduceNatDecEq (Nat.decEq _ _) := fun _ => return .continue

/-- Evaluates the multiplication of two natural number literals during `cbv`. -/
scoped cbv_simproc cbv_eval cbvEvaluateMultiplicationOfTwoLiterals (HMul.hMul (_ : Nat) (_ : Nat)) :=
  fun _ => return .continue

cbv_simproc_decl cbvInactiveReduceIdentityFunction (id _) := fun _ => return .continue

cbv_simproc_decl cbvReduceApplicationOfAnEtaExpandedClosureToItsArgument (Function.comp _ _ _) :=
  fun e => do
    let_expr Function.comp _ _ _ f g a := e | return .continue
    return .visit { expr := mkApp f (mkApp g a) }

builtin_cbv_simproc builtinCbvReduceNatAdd (HAdd.hAdd _ _) := fun _ => return .continue

builtin_cbv_simproc cbv_eval builtinCbvEvalReduceStringLength (String.length _) :=
  fun _ => return .continue

builtin_cbv_simproc_decl builtinCbvInactiveReduceNatAdd (HAdd.hAdd _ _) := fun _ => return .continue

builtin_cbv_simproc_decl builtinCbvReduceComparisonOfTwoNaturalNumberLiterals (Nat.blt _ _) :=
  fun _ => return .continue

end CbvSimproc

section Patterns

simproc_pattern% (And _ _) => inactiveShortCircuitAnd

simproc_pattern% (Nat.rec (motive := fun _ => Nat) _ _ _) =>
  reduceApplicationOfAVeryLongIdentifierName

builtin_simproc_pattern% (HSub.hSub _ _) => builtinInactiveReduceNatSub

builtin_simproc_pattern% (HAppend.hAppend (_ : String) (_ : String) (_ : String) _ _ _) =>
  builtinReduceStringAppendOnLiteralArguments

cbv_simproc_pattern% (id _) => cbvInactiveReduceIdentityFunction

cbv_simproc_pattern% (Function.comp (_ : Nat → Nat) (_ : Nat → Nat) (_ : Nat)) =>
  cbvReduceApplicationOfAnEtaExpandedClosureToItsArgument

builtin_cbv_simproc_pattern% (HAdd.hAdd _ _) => builtinCbvInactiveReduceNatAdd

builtin_cbv_simproc_pattern% (Nat.blt (_ : Nat) (_ : Nat)) =>
  builtinCbvReduceComparisonOfTwoNaturalNumberLiterals

end Patterns

section Attrs

attribute [simproc] inactiveShortCircuitAnd

attribute [simproc ↓] inactiveShortCircuitAnd

attribute [scoped simproc ↑] reduceApplicationOfAVeryLongIdentifierName

attribute [sevalproc] inactiveDropUnitArgument

attribute [local sevalproc ↓] reduceDefinitionalProjectionOfAnExplicitlyConstructedPair

attribute [builtin_simproc] builtinInactiveReduceNatSub

attribute [builtin_simproc ↑] builtinReduceStringAppendOnLiteralArguments

attribute [builtin_sevalproc] builtinInactiveDropUnitArgument

attribute [builtin_sevalproc ↓] builtinReduceIdentityCoercionBetweenIntegerTypes

attribute [cbv_simproc] cbvInactiveReduceIdentityFunction

attribute [cbv_simproc cbv_eval] cbvReduceApplicationOfAnEtaExpandedClosureToItsArgument

attribute [builtin_cbv_simproc] builtinCbvInactiveReduceNatAdd

attribute [scoped builtin_cbv_simproc ↓] builtinCbvReduceComparisonOfTwoNaturalNumberLiterals

end Attrs

end SimprocTests
