import Lean

/-!
Tests for the formatters of the `Sym.simp` and `Sym.dsimp` DSLs (`Init.Sym.Simp.SimprocDSL` and
`Init.Sym.DSimp.DSimprocDSL`): the `register_sym_simp` and `register_sym_dsimp` commands with
their `pre`, `post`, `maxSteps` and `maxDischargeDepth` fields, the `rewrite` simprocs with named
theorem sets and inline theorem lists, their optional `with` dischargers, and parenthesized
simproc and discharger expressions. The examples range from variants that fit on a single line to
chains that have to be broken in several places.
-/

open Lean Meta

namespace SymSimprocDSLTests

theorem natZeroAdd (n : Nat) : 0 + n = n := Nat.zero_add n

theorem natAddZero (n : Nat) : n + 0 = n := Nat.add_zero n

theorem natMulOne (n : Nat) : n * 1 = n := Nat.mul_one n

theorem natOneMul (n : Nat) : 1 * n = n := Nat.one_mul n

theorem natSuccAdd (n m : Nat) : n.succ + m = (n + m).succ := Nat.succ_add n m

theorem natAddSucc (n m : Nat) : n + m.succ = (n + m).succ := Nat.add_succ n m

theorem listAppendNil (xs : List α) : xs ++ [] = xs := List.append_nil xs

theorem listNilAppend (xs : List α) : [] ++ xs = xs := List.nil_append xs

section DSimpVariants

register_sym_dsimp emptyDSimp where

register_sym_dsimp betaOnlyDSimp where
  pre := beta

register_sym_dsimp reduceProjectionsAndMatches where
  pre  := match >> proj
  post := beta >> zeta

register_sym_dsimp expandLetDeclarations where
  pre  := ground
  post := zeta >> zeta_delta
  maxSteps := 50000

register_sym_dsimp preferMatchesOverProjections where
  pre := match <|> proj <|> beta <|> none

register_sym_dsimp parenthesizedDSimpChains where
  pre  := (beta >> zeta) <|> (proj >> match)
  post := ((ground <|> beta) >> zeta_delta) <|> none

register_sym_dsimp aDSimpVariantWhoseNameIsLongEnoughToPushTheWhereKeywordOntoTheLineBelowTheDeclaration where
  pre := ground

register_sym_dsimp normalizeGroundTermsProjectionsAndMatchExpressions where
  pre := ground >> beta >> zeta >> zeta_delta >> proj >> match >> beta >> zeta >> proj >> match
  post := (ground >> beta) <|> (zeta >> zeta_delta) <|> (proj >> match) <|> (beta >> ground) <|> none
  maxSteps := 1000000

register_sym_dsimp reduceEveryDefinitionalRedexInTheGoal where
  pre := (((ground >> beta) >> (zeta >> zeta_delta)) >> ((proj >> match) >> (beta >> ground))) <|> none

end DSimpVariants

section SimpVariants

register_sym_simp emptySimp where

register_sym_simp groundSimp where
  post := ground

register_sym_simp telescopeThenGround where
  pre  := telescope
  post := ground

register_sym_simp controlAndArrowTelescopes where
  pre  := control <|> arrow_telescope
  post := ground >> self

register_sym_simp rewriteWithNamedSet where
  post := rewrite sym_simp

register_sym_simp rewriteWithNamedSetAndGrindDischarger where
  post := rewrite sym_simp with grind

register_sym_simp rewriteWithInlineTheorems where
  post := rewrite [natZeroAdd, natAddZero]

register_sym_simp rewriteWithInlineTheoremsAndSelfDischarger where
  pre  := telescope
  post := rewrite [natZeroAdd, natAddZero, natMulOne] with self
  maxSteps := 50000
  maxDischargeDepth := 4

register_sym_simp rewriteWithoutDischarge where
  post := rewrite [listAppendNil, listNilAppend] with none

register_sym_simp parenthesizedSimpChains where
  pre  := (control <|> arrow_telescope) >> telescope
  post := (rewrite sym_simp with (grind)) <|> (ground >> self)

register_sym_simp parenthesizedDischargers where
  post := rewrite sym_simp with ((self)) <|> rewrite [natMulOne] with ((none))

register_sym_simp aSimpVariantWhoseNameIsLongEnoughToPushTheWhereKeywordOntoTheLineBelowTheDeclaration where
  post := ground

register_sym_simp normalizeArithmeticOnNaturalNumbers where
  post := rewrite [natZeroAdd, natAddZero, natMulOne, natOneMul, natSuccAdd, natAddSucc] with self

register_sym_simp normalizeArithmeticAndListOperations where
  pre  := control <|> arrow_telescope <|> telescope
  post := rewrite [natZeroAdd, natAddZero, natMulOne, natOneMul, natSuccAdd, natAddSucc, listAppendNil, listNilAppend] with grind
  maxSteps := 200000
  maxDischargeDepth := 8

register_sym_simp rewriteWithTheDefaultTheoremSetAndAGrindDischarger where
  pre  := telescope >> control
  post := ground >> rewrite sym_simp with grind >> self

register_sym_simp discriminateBetweenControlFlowAndArithmetic where
  pre := control >> (rewrite sym_simp with grind) <|> arrow_telescope >> (rewrite [natZeroAdd] with self)
  post := ((ground >> telescope) <|> (self >> ground)) >> (rewrite sym_simp with (grind)) <|> none

end SimpVariants

end SymSimprocDSLTests
