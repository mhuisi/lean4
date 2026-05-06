import Lean

/-!
Tests for the `grind` lint and propagator formatters: the `#grind_lint check`, `#grind_lint
inspect`, `#grind_lint mute` and `#grind_lint skip` commands (`fmtGrindLintCheck`,
`fmtGrindLintInspect`, `fmtGrindLintMute`, `fmtGrindLintSkip`), the `grind_propagator` and
`builtin_grind_propagator` commands (`fmtGrindPropagator`, `fmtBuiltinGrindPropagator`), and the
`builtin_grind_propagator` attribute (`fmtGrindPropagatorBuiltinAttr`).
The examples exercise the optional configuration items, the optional `in`/`in module` restriction,
the optional `suffix` modifier, both `↓`/`↑` directions, doc comments, and identifier lists and
propagator bodies of varying length so that the layout has to break in different places.
-/

open Lean Meta Grind

namespace GrindLintPropagatorTests

section GrindLintCheck

#grind_lint check

#grind_lint check in GrindLintPropagatorTests

#grind_lint check (min := 20) in GrindLintPropagatorTests

#grind_lint check (min := 20) (detailed := 100) in GrindLintPropagatorTests

#grind_lint check +mbtc -lookahead (min := 20) in GrindLintPropagatorTests

#grind_lint check in module Init.Grind.Lint

#grind_lint check (detailed := 250) in module Init.Grind.Lint Init.Grind.Propagator

#grind_lint check (min := 30) (detailed := 250) in GrindLintPropagatorTests SomeOtherNamespace
  YetAnotherNamespace

#grind_lint check (min := 30) (detailed := 250) (ematch := 40) (instances := 200) (gen := 15)
  in module Init.Grind.Lint Init.Grind.Propagator Init.Grind.Tactics Init.Grind.Attr

#grind_lint check (min := 30) (detailed := 250) (ematch := 40) (instances := 200) (gen := 15)
  (splits := 2) (lookahead := false) in module Init.Data.Array.Lemmas Init.Data.List.Lemmas
  Init.Data.Option.Lemmas Init.Data.BitVec.Lemmas

end GrindLintCheck

section GrindLintInspect

#grind_lint inspect Array.zip_map

#grind_lint inspect Array.zip_map List.getLast?_concat Array.range_succ

#grind_lint inspect (min := 5) Array.zip_map

#grind_lint inspect (min := 5) (detailed := 15) Array.zip_map List.getLast?_concat

#grind_lint inspect (min := 5) (detailed := 15) (ematch := 30) Array.reverse_flatMap
  Array.setIfInBounds_empty List.append_sublist_append_left List.sublist_append_of_sublist_right

#grind_lint inspect (min := 5) (detailed := 15) (ematch := 30) (instances := 150) (gen := 12)
  (splits := 1) BitVec.toInt_eq_toNat_bmod BitVec.toNat_sshiftRight' BitVec.msb_rotateRight
  BitVec.getLsbD_abs BitVec.msb_extractLsb' ListSlice.size_mkSlice_rcc

end GrindLintInspect

section GrindLintMuteAndSkip

#grind_lint mute Array.zip_map

#grind_lint mute Array.zip_map Int.zero_shiftRight

#grind_lint mute Array.back?_mapIdx List.getLast?_zipIdx List.lt_of_range'_eq_append_cons
  BitVec.toInt_eq_toNat_of_msb ListSlice.size_mkSlice_roc Array.findFinIdx?_empty

#grind_lint skip Array.range_succ

#grind_lint skip suffix append

#grind_lint skip Array.range_succ Array.range'_succ List.range'_append_1

#grind_lint skip suffix append reverse flatten zipIdx mapIdx

#grind_lint skip Array.reverse_extract Array.extract_reverse List.reverse_sublist
  List.flatten_singleton BitVec.msb_replicate BitVec.toInt_rotateLeft Fin.castSucc_succ

end GrindLintMuteAndSkip

section GrindPropagator

grind_propagator ↑ propagateNotUp (Not) := fun _ => return ()

grind_propagator ↓ propagateAndDown (And) := fun e => do
  let_expr And _ _ := e | return ()
  return ()

/--
Propagates equalities upwards through the boolean `or` connective, so that a truth value known for
the disjunction is available for its arguments.
-/
grind_propagator ↑ propagateOrUp (Or) := fun e => do
  let_expr Or a b := e | return ()
  let _ ← pure a
  let _ ← pure b
  return ()

grind_propagator ↓ propagateVeryLongPropagatorNameForTheIteConnective (ite) := fun _ => return ()

grind_propagator ↑ propagateAnEvenLongerPropagatorNameForTheConditionalConnective (dite) :=
  fun _ => return ()

end GrindPropagator

section BuiltinGrindPropagator

builtin_grind_propagator propagateNotDown ↓Not := fun _ => return ()

builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And _ _ := e | return ()
  return ()

/-- Propagates the truth value of an equality to its arguments. -/
builtin_grind_propagator propagateEqDown ↓Eq := fun _ => return ()

builtin_grind_propagator propagateSomewhatLongPropagatorNameDown ↓GrindLintPropagatorTests.Foo :=
  fun _ => return ()

builtin_grind_propagator propagateAnExceedinglyLongPropagatorNameUp
    ↑GrindLintPropagatorTests.SomeNamespace.SomeVeryLongOperatorName := fun _ => return ()

builtin_grind_propagator propagateBooleanEqualityUp ↑BEq.beq := fun e => do
  let_expr BEq.beq _ _ lhs rhs := e | return ()
  let _ ← pure lhs
  let _ ← pure rhs
  return ()

end BuiltinGrindPropagator

section GrindPropagatorBuiltinAttr

def somePropagator : Propagator := fun _ => return ()

attribute [builtin_grind_propagator ↓Not] somePropagator

attribute [builtin_grind_propagator ↑And] somePropagator

attribute [builtin_grind_propagator ↑GrindLintPropagatorTests.SomeNamespace.SomeVeryLongName]
  somePropagator

end GrindPropagatorBuiltinAttr

end GrindLintPropagatorTests
