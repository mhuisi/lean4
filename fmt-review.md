# Formatter review

<!-- fmt-review: generated, begin. Edit with fmt_review.py; edits here are lost. -->

This file tracks the changes to parsers and formatters in `master` since the last manual review of the auto-formatter. The `fmt-review` skill (`.claude/skills/fmt-review/SKILL.md`) gives the procedure. `fmt-review.json` holds the same data for tools.

| | |
|---|---|
| Reference (last review) | `0f708979a3c5` chore: update stage0 (2026-11-23), reviewed 2026-11-24 |
| Target (last refresh) | `0f708979a3c5` chore: update stage0 (2026-11-23), refreshed 2026-11-24 |
| Commits since the reference | 0 |
| Local changes in the build | none |
| Items | none |
| Syntax without a formatter | 178 kinds, 101 of them not matched by a formatter (and 45 generic kinds, 0 exempt kinds), of 1669 kinds |
| Lint of changed files | not run for this target |

## Open items (0)

None.

## Decided items of this review (0)

None.

## Items carried from earlier reviews (0)

None.

## Syntax without a formatter (178)

These syntax node kinds have no formatter. Where such a node reaches `fmt`, the output keeps its input layout. The list leaves out 12 private kinds (`local` syntax, which cannot have a formatter), 45 generic kinds and 0 exempt kinds.

### Not matched by a formatter (101)

No formatter code mentions these kinds. They need a formatter of their own.

- [Init.BinderPredicates](src/Init/BinderPredicates.lean) (1):
  - [`binderPred.quot`](src/Init/BinderPredicates.lean#L18)
- [Init.Conv](src/Init/Conv.lean) (1):
  - [`conv.quot`](src/Init/Conv.lean#L18)
- [Init.Grind.Attr](src/Init/Grind/Attr.lean) (1):
  - [`grind_mod.quot`](src/Init/Grind/Attr.lean#L315)
- [Init.Grind.Interactive](src/Init/Grind/Interactive.lean) (3):
  - [`grind.quot`](src/Init/Grind/Interactive.lean#L47)
  - [`grind_filter.quot`](src/Init/Grind/Interactive.lean#L29)
  - [`grind_ref.quot`](src/Init/Grind/Interactive.lean#L115)
- [Init.Grind.Tactics](src/Init/Grind/Tactics.lean) (1):
  - [`Lean.Parser.Tactic.grindNorm`](src/Init/Grind/Tactics.lean#L319) (tactic)
- [Init.Notation](src/Init/Notation.lean) (1):
  - [`rawStx.quot`](src/Init/Notation.lean#L608)
- [Init.RCases](src/Init/RCases.lean) (2):
  - [`rcasesPat.quot`](src/Init/RCases.lean#L65)
  - [`rintroPat.quot`](src/Init/RCases.lean#L90)
- [Init.Sym.DSimp.DSimprocDSL](src/Init/Sym/DSimp/DSimprocDSL.lean) (2):
  - [`sym_dsimp_field.quot`](src/Init/Sym/DSimp/DSimprocDSL.lean#L86)
  - [`sym_dsimproc.quot`](src/Init/Sym/DSimp/DSimprocDSL.lean#L31)
- [Init.Sym.Simp.SimprocDSL](src/Init/Sym/Simp/SimprocDSL.lean) (3):
  - [`sym_discharger.quot`](src/Init/Sym/Simp/SimprocDSL.lean#L44)
  - [`sym_simp_field.quot`](src/Init/Sym/Simp/SimprocDSL.lean#L128)
  - [`sym_simproc.quot`](src/Init/Sym/Simp/SimprocDSL.lean#L43)
- [Init.Tactics](src/Init/Tactics.lean) (1):
  - [`Lean.Parser.Tactic.tripleNotationMacro`](src/Init/Tactics.lean#L2543) (term)
- [Lean.Data.Html.Syntax](src/Lean/Data/Html/Syntax.lean) (11):
  - [`Lean.Html.Syntax.attr`](src/Lean/Data/Html/Syntax.lean#L407)
  - [`Lean.Html.Syntax.attrName`](src/Lean/Data/Html/Syntax.lean#L359)
  - [`Lean.Html.Syntax.attrVal`](src/Lean/Data/Html/Syntax.lean#L378)
  - [`Lean.Html.Syntax.comment`](src/Lean/Data/Html/Syntax.lean#L320)
  - [`Lean.Html.Syntax.content`](src/Lean/Data/Html/Syntax.lean#L533)
  - [`Lean.Html.Syntax.element`](src/Lean/Data/Html/Syntax.lean#L579)
  - [`Lean.Html.Syntax.interp`](src/Lean/Data/Html/Syntax.lean#L181)
  - [`Lean.Html.Syntax.interpMany`](src/Lean/Data/Html/Syntax.lean#L185)
  - [`Lean.Html.Syntax.tagName`](src/Lean/Data/Html/Syntax.lean#L341)
  - [`Lean.Html.Syntax.text`](src/Lean/Data/Html/Syntax.lean#L212)
  - [`Lean.Html.Syntax.«html%»`](src/Lean/Data/Html/Syntax.lean#L652) (term)
- [Lean.Data.Json.Elab](src/Lean/Data/Json/Elab.lean) (1):
  - [`json.quot`](src/Lean/Data/Json/Elab.lean#L35)
- [Lean.DocString.Syntax](src/Lean/DocString/Syntax.lean) (53):
  - [`Lean.Doc.Parser.Arg.anon`](src/Lean/DocString/Syntax.lean#L402)
  - [`Lean.Doc.Parser.Arg.flag_off`](src/Lean/DocString/Syntax.lean#L420)
  - [`Lean.Doc.Parser.Arg.flag_on`](src/Lean/DocString/Syntax.lean#L415)
  - [`Lean.Doc.Parser.Arg.named`](src/Lean/DocString/Syntax.lean#L406)
  - [`Lean.Doc.Parser.Arg.named_no_paren`](src/Lean/DocString/Syntax.lean#L411)
  - [`Lean.Doc.Parser.ArgVal.ident`](src/Lean/DocString/Syntax.lean#L383)
  - [`Lean.Doc.Parser.ArgVal.num`](src/Lean/DocString/Syntax.lean#L386)
  - [`Lean.Doc.Parser.ArgVal.str`](src/Lean/DocString/Syntax.lean#L380)
  - [`Lean.Doc.Parser.Block.blockquote`](src/Lean/DocString/Syntax.lean#L882)
  - [`Lean.Doc.Parser.Block.codeblock`](src/Lean/DocString/Syntax.lean#L887)
  - [`Lean.Doc.Parser.Block.command`](src/Lean/DocString/Syntax.lean#L974)
  - [`Lean.Doc.Parser.Block.directive`](src/Lean/DocString/Syntax.lean#L919)
  - [`Lean.Doc.Parser.Block.dl`](src/Lean/DocString/Syntax.lean#L879)
  - [`Lean.Doc.Parser.Block.footnote_ref`](src/Lean/DocString/Syntax.lean#L964)
  - [`Lean.Doc.Parser.Block.header`](src/Lean/DocString/Syntax.lean#L951)
  - [`Lean.Doc.Parser.Block.link_ref`](src/Lean/DocString/Syntax.lean#L959)
  - [`Lean.Doc.Parser.Block.metadata_block`](src/Lean/DocString/Syntax.lean#L969)
  - [`Lean.Doc.Parser.Block.ol`](src/Lean/DocString/Syntax.lean#L876)
  - [`Lean.Doc.Parser.Block.para`](src/Lean/DocString/Syntax.lean#L870)
  - [`Lean.Doc.Parser.Block.ul`](src/Lean/DocString/Syntax.lean#L873)
  - [`Lean.Doc.Parser.DescItem.item`](src/Lean/DocString/Syntax.lean#L862)
  - [`Lean.Doc.Parser.Inline.bold`](src/Lean/DocString/Syntax.lean#L705)
  - [`Lean.Doc.Parser.Inline.code`](src/Lean/DocString/Syntax.lean#L714)
  - [`Lean.Doc.Parser.Inline.display_math`](src/Lean/DocString/Syntax.lean#L730)
  - [`Lean.Doc.Parser.Inline.emph`](src/Lean/DocString/Syntax.lean#L698)
  - [`Lean.Doc.Parser.Inline.footnote`](src/Lean/DocString/Syntax.lean#L749)
  - [`Lean.Doc.Parser.Inline.image`](src/Lean/DocString/Syntax.lean#L739)
  - [`Lean.Doc.Parser.Inline.inline_math`](src/Lean/DocString/Syntax.lean#L727)
  - [`Lean.Doc.Parser.Inline.linebreak`](src/Lean/DocString/Syntax.lean#L756)
  - [`Lean.Doc.Parser.Inline.link`](src/Lean/DocString/Syntax.lean#L733)
  - [`Lean.Doc.Parser.Inline.role`](src/Lean/DocString/Syntax.lean#L757)
  - [`Lean.Doc.Parser.Inline.text`](src/Lean/DocString/Syntax.lean#L697)
  - [`Lean.Doc.Parser.LinkTarget.ref`](src/Lean/DocString/Syntax.lean#L444)
  - [`Lean.Doc.Parser.LinkTarget.url`](src/Lean/DocString/Syntax.lean#L439)
  - [`Lean.Doc.Parser.ListItem.item`](src/Lean/DocString/Syntax.lean#L854)
  - [`Lean.Doc.Parser.boldDelimiter`](src/Lean/DocString/Syntax.lean#L555)
  - [`Lean.Doc.Parser.codeBlockFence`](src/Lean/DocString/Syntax.lean#L568)
  - [`Lean.Doc.Parser.codeDelimiter`](src/Lean/DocString/Syntax.lean#L560)
  - [`Lean.Doc.Parser.directiveDelimiter`](src/Lean/DocString/Syntax.lean#L588)
  - [`Lean.Doc.Parser.displayMathMarker`](src/Lean/DocString/Syntax.lean#L583)
  - [`Lean.Doc.Parser.document`](src/Lean/DocString/Syntax.lean#L992)
  - [`Lean.Doc.Parser.emphDelimiter`](src/Lean/DocString/Syntax.lean#L550)
  - [`Lean.Doc.Parser.headerMarker`](src/Lean/DocString/Syntax.lean#L518)
  - [`Lean.Doc.Parser.inlineMathMarker`](src/Lean/DocString/Syntax.lean#L575)
  - [`Lean.Doc.Parser.listMarker`](src/Lean/DocString/Syntax.lean#L525)
  - [`Lean.Doc.Parser.versoCode`](src/Lean/DocString/Syntax.lean#L85)
  - [`Lean.Doc.Parser.versoCodeBlock`](src/Lean/DocString/Syntax.lean#L93)
  - [`Lean.Doc.Parser.versoCodeLine`](src/Lean/DocString/Syntax.lean#L89)
  - [`Lean.Doc.Parser.versoImageAlt`](src/Lean/DocString/Syntax.lean#L81)
  - [`Lean.Doc.Parser.versoLinkRefUrl`](src/Lean/DocString/Syntax.lean#L77)
  - [`Lean.Doc.Parser.versoLinkUrl`](src/Lean/DocString/Syntax.lean#L73)
  - [`Lean.Doc.Parser.versoRef`](src/Lean/DocString/Syntax.lean#L69)
  - [`Lean.Doc.Parser.versoText`](src/Lean/DocString/Syntax.lean#L65)
- [Lean.Parser.Command](src/Lean/Parser/Command.lean) (7):
  - [`Lean.Parser.Command.InternalSyntax.end_local_scope`](src/Lean/Parser/Command.lean#L389)
  - [`Lean.Parser.Command.InternalSyntax.without_check_deprecated`](src/Lean/Parser/Command.lean#L399)
  - [`Lean.Parser.Command.contractDeclVal`](src/Lean/Parser/Command.lean#L210)
  - [`Lean.Parser.Command.ensuresClause`](src/Lean/Parser/Command.lean#L143)
  - [`Lean.Parser.Command.givenClause`](src/Lean/Parser/Command.lean#L132)
  - [`Lean.Parser.Command.requiresClause`](src/Lean/Parser/Command.lean#L138)
  - [`Lean.Parser.Command.throwsClause`](src/Lean/Parser/Command.lean#L146)
- [Lean.Parser.Do](src/Lean/Parser/Do.lean) (5):
  - [`Lean.Parser.Term.doAssertion`](src/Lean/Parser/Do.lean#L295) (doElem)
  - [`Lean.Parser.Term.doErased`](src/Lean/Parser/Do.lean#L112) (doElem)
  - [`Lean.Parser.Term.doErasedArrow`](src/Lean/Parser/Do.lean#L115) (doElem)
  - [`Lean.Parser.Term.doLoopDecreasing`](src/Lean/Parser/Do.lean#L199)
  - [`Lean.Parser.Term.doLoopInvariant`](src/Lean/Parser/Do.lean#L187)
- [Lean.Parser.Term](src/Lean/Parser/Term.lean) (2):
  - [`Lean.Parser.Command.commentBody`](src/Lean/Parser/Term.lean#L177)
  - [`Lean.Parser.Command.versoCommentBody`](src/Lean/Parser/Term.lean#L115)
- [Lean.Parser.Term.Basic](src/Lean/Parser/Term/Basic.lean) (1):
  - [`Lean.Parser.Tactic.seq1`](src/Lean/Parser/Term/Basic.lean#L95)
- [Std.Tactic.Do.Syntax](src/Std/Tactic/Do/Syntax.lean) (4):
  - [`mcasesPat.quot`](src/Std/Tactic/Do/Syntax.lean#L225)
  - [`mintroPat.quot`](src/Std/Tactic/Do/Syntax.lean#L312)
  - [`mrefinePat.quot`](src/Std/Tactic/Do/Syntax.lean#L272)
  - [`mrevertPat.quot`](src/Std/Tactic/Do/Syntax.lean#L331)
- [Std.WP.Tactic](src/Std/WP/Tactic.lean) (1):
  - [`vcgenDischarge.quot`](src/Std/WP/Tactic.lean#L73)

### Matched by the formatter of other syntax (77)

The code of another formatter mentions these kinds, usually in an antiquotation pattern of the parent syntax. Such a formatter handles the node without `fmt`. A node in another place keeps its input layout.

- [Init.Notation](src/Init/Notation.lean) (1):
  - [`Lean.reduceConfig`](src/Init/Notation.lean#L770), in `Lean.Fmt.fmtReduceCmd`, `Lean.Fmt.fmtReduceConfig`
- [Init.NotationExtra](src/Init/NotationExtra.lean) (3):
  - [`Lean.calcSteps`](src/Init/NotationExtra.lean#L102), in `Lean.Fmt.fmtCalc`, `Lean.Fmt.fmtCalcTactic`, `Lean.Fmt.fmtCalcTerm` +1
  - [`Lean.explicitBinders`](src/Init/NotationExtra.lean#L23), in `Lean.Fmt.explicitBindersToGroup`, `Lean.Fmt.fmtExists`, `Lean.Fmt.fmtExistsKeyword` +4
  - [`Lean.unifConstraintElem`](src/Init/NotationExtra.lean#L67), in `Lean.Fmt.fmtUnifHint`
- [Init.Tactics](src/Init/Tactics.lean) (13):
  - [`Lean.Parser.Tactic.SolveByElim.args`](src/Init/Tactics.lean#L1716), in `Lean.Fmt.fmtApplyAssumption`, `Lean.Fmt.fmtApplyRules`, `Lean.Fmt.fmtSolveByElim`
  - [`Lean.Parser.Tactic.SolveByElim.using_`](src/Init/Tactics.lean#L1718), in `Lean.Fmt.fmtApplyAssumption`, `Lean.Fmt.fmtApplyRules`, `Lean.Fmt.fmtSolveByElim`
  - [`Lean.Parser.Tactic.dsimpArgs`](src/Init/Tactics.lean#L763), in `Lean.Fmt.fmtConvDSimpTrace`, `Lean.Fmt.fmtWithDSimpTraceArgsRest`, `Lean.Fmt.fmtWithSimpAllTraceArgsRest`
  - [`Lean.Parser.Tactic.dsimpTraceArgsRest`](src/Init/Tactics.lean#L794), in `Lean.Fmt.fmtDSimpTrace`, `Lean.Fmt.fmtDSimpTraceBang`, `Lean.Fmt.fmtWithDSimpTraceArgsRest`
  - [`Lean.Parser.Tactic.inductionAlt`](src/Init/Tactics.lean#L1008), in `Lean.Fmt.fmtInductionAlt`, `Lean.Fmt.fmtWithInductionAlts`
  - [`Lean.Parser.Tactic.inductionAlts`](src/Init/Tactics.lean#L1013), in `Lean.Fmt.fmtFunCases`, `Lean.Fmt.fmtFunInduction`, `Lean.Fmt.fmtInductionLike` +3
  - [`Lean.Parser.Tactic.locationHyp`](src/Init/Tactics.lean#L526), in `Lean.Fmt.fmtLocation`
  - [`Lean.Parser.Tactic.optConfig`](src/Init/Tactics.lean#L30), in `Lean.Fmt.fmtApply?`, `Lean.Fmt.fmtApplyAssumption`, `Lean.Fmt.fmtApplyRules` +76
  - [`Lean.Parser.Tactic.simpAllTraceArgsRest`](src/Init/Tactics.lean#L785), in `Lean.Fmt.fmtSimpAllTrace`, `Lean.Fmt.fmtSimpAllTraceBang`, `Lean.Fmt.fmtWithSimpAllTraceArgsRest`
  - [`Lean.Parser.Tactic.simpArgs`](src/Init/Tactics.lean#L754), in `Lean.Fmt.fmtConvSimpTrace`, `Lean.Fmt.fmtWithSimpTraceArgsRest`, `Lean.Fmt.fmtWithSimpaArgsRest` +1
  - [`Lean.Parser.Tactic.simpTraceArgsRest`](src/Init/Tactics.lean#L766), in `Lean.Fmt.fmtSimpTrace`, `Lean.Fmt.fmtSimpTraceBang`, `Lean.Fmt.fmtWithSimpTraceArgsRest`
  - [`Lean.Parser.Tactic.simpaArgsRest`](src/Init/Tactics.lean#L803), in `Lean.Fmt.fmtSimpa`, `Lean.Fmt.fmtSimpaBang`, `Lean.Fmt.fmtSimpaQuestion` +2
  - [`Lean.Parser.Tactic.simpaUsingBangArgsRest`](src/Init/Tactics.lean#L830), in `Lean.Fmt.fmtSimpaBangUsingBang`, `Lean.Fmt.fmtSimpaQuestionBangUsingBang`, `Lean.Fmt.fmtSimpaQuestionUsingBang` +2
- [Lake.DSL.DeclUtil](src/lake/Lake/DSL/DeclUtil.lean) (5):
  - [`Lake.DSL.declValDo`](src/lake/Lake/DSL/DeclUtil.lean#L66), in `Lake.Formatters.fmtPostUpdateDecl`, `Lake.Formatters.fmtScriptDecl`
  - [`Lake.DSL.declValStruct`](src/lake/Lake/DSL/DeclUtil.lean#L69), in `Lake.Formatters.fmtWithOptConfig`
  - [`Lake.DSL.declValWhere`](src/lake/Lake/DSL/DeclUtil.lean#L72), in `Lake.Formatters.fmtWithOptConfig`
  - [`Lake.DSL.optConfig`](src/lake/Lake/DSL/DeclUtil.lean#L78), in `Lake.Formatters.fmtInputDirCommand`, `Lake.Formatters.fmtInputFileCommand`, `Lake.Formatters.fmtLeanExeCommand` +3
  - [`Lake.DSL.structVal`](src/lake/Lake/DSL/DeclUtil.lean#L63), in `Lake.Formatters.fmtWithOptConfig`
- [Lake.DSL.Syntax](src/lake/Lake/DSL/Syntax.lean) (6):
  - [`Lake.DSL.buildDeclSig`](src/lake/Lake/DSL/Syntax.lean#L201), in `Lake.Formatters.fmtLibraryFacetDecl`, `Lake.Formatters.fmtModuleFacetDecl`, `Lake.Formatters.fmtPackageFacetDecl` +2
  - [`Lake.DSL.cmdDo`](src/lake/Lake/DSL/Syntax.lean#L459), in `Lake.Formatters.MetaIf.mk`, `Lake.Formatters.deconstructMetaIf?`, `Lake.Formatters.fmtMetaIfBranch` +1
  - [`Lake.DSL.depSpec`](src/lake/Lake/DSL/Syntax.lean#L161), in `Lake.Formatters.fmtRequireDecl`
  - [`Lake.DSL.externLibDeclSpec`](src/lake/Lake/DSL/Syntax.lean#L350), in `Lake.Formatters.fmtExternLibCommand`
  - [`Lake.DSL.scriptDeclSpec`](src/lake/Lake/DSL/Syntax.lean#L396), in `Lake.Formatters.fmtScriptDecl`
  - [`Lake.DSL.verClause`](src/lake/Lake/DSL/Syntax.lean#L151), in `Lake.Formatters.fmtRequireDecl`
- [Lean.Elab.ConfigEval.Commands](src/Lean/Elab/ConfigEval/Commands.lean) (1):
  - [`Lean.Elab.ConfigEval.configEntries`](src/Lean/Elab/ConfigEval/Commands.lean#L71), in `Lean.Fmt.fmtDeclareCommandConfig`, `Lean.Fmt.fmtDeclareConfig`, `Lean.Fmt.fmtDeclareCoreConfigElab` +4
- [Lean.Meta.Tactic.Grind.Parser](src/Lean/Meta/Tactic/Grind/Parser.lean) (1):
  - [`Lean.Parser.Command.grindPatternCnstrs`](src/Lean/Meta/Tactic/Grind/Parser.lean#L35), in `Lean.Fmt.fmtGrindPattern`
- [Lean.Parser.Command](src/Lean/Parser/Command.lean) (13):
  - [`Lean.Parser.Command.declModifiers`](src/Lean/Parser/Command.lean#L100), in `Lake.Formatters.fmtConfigDecl`, `Lake.Formatters.fmtConfigField`, `Lean.Fmt.fmtClassAbbrev` +11
  - [`Lean.Parser.Command.declSig`](src/Lean/Parser/Command.lean#L128), in `Lake.Formatters.fmtConfigField`, `Lean.Fmt.fmtAxiom`, `Lean.Fmt.fmtInstance` +4
  - [`Lean.Parser.Command.declValEqns`](src/Lean/Parser/Command.lean#L194), in `Lake.Formatters.fmtCacheServiceCommand`, `Lean.Fmt.fmtAbbrev`, `Lean.Fmt.fmtDefinition` +4
  - [`Lean.Parser.Command.declValSimple`](src/Lean/Parser/Command.lean#L192), in `Lake.Formatters.fmtCacheServiceCommand`, `Lake.Formatters.fmtExternLibCommand`, `Lake.Formatters.fmtPostUpdateDecl` +9
  - [`Lean.Parser.Command.openHiding`](src/Lean/Parser/Command.lean#L811), in `Lean.Fmt.fmtOpenDecl`
  - [`Lean.Parser.Command.openOnly`](src/Lean/Parser/Command.lean#L817), in `Lean.Fmt.fmtOpenDecl`
  - [`Lean.Parser.Command.openRenaming`](src/Lean/Parser/Command.lean#L815), in `Lean.Fmt.fmtOpenDecl`
  - [`Lean.Parser.Command.openScoped`](src/Lean/Parser/Command.lean#L821), in `Lean.Fmt.fmtOpenDecl`
  - [`Lean.Parser.Command.openSimple`](src/Lean/Parser/Command.lean#L819), in `Lean.Fmt.fmtOpenDecl`
  - [`Lean.Parser.Command.optDeclSig`](src/Lean/Parser/Command.lean#L153), in `Lean.Fmt.fmtAbbrev`, `Lean.Fmt.fmtClassInductive`, `Lean.Fmt.fmtCoinductive` +8
  - [`Lean.Parser.Command.sectionHeader`](src/Lean/Parser/Command.lean#L336), in `Lean.Fmt.fmtSection`
  - [`Lean.Parser.Command.structFields`](src/Lean/Parser/Command.lean#L295), in `Lean.Fmt.fmtStructure`
  - [`Lean.Parser.Command.whereStructInst`](src/Lean/Parser/Command.lean#L196), in `Lake.Formatters.fmtCacheServiceCommand`, `Lean.Fmt.fmtAbbrev`, `Lean.Fmt.fmtDefinition` +4
- [Lean.Parser.Do](src/Lean/Parser/Do.lean) (8):
  - [`Lean.Parser.Term.doCatch`](src/Lean/Parser/Do.lean#L233), in `Lean.Fmt.fmtDoTry`, `Lean.Fmt.fmtTermTry`, `Lean.Fmt.fmtTryCatchFinally`
  - [`Lean.Parser.Term.doCatchMatch`](src/Lean/Parser/Do.lean#L235), in `Lean.Fmt.fmtDoTry`, `Lean.Fmt.fmtTermTry`, `Lean.Fmt.fmtTryCatchFinally`
  - [`Lean.Parser.Term.doFinally`](src/Lean/Parser/Do.lean#L237), in `Lean.Fmt.fmtDoTry`, `Lean.Fmt.fmtTermTry`, `Lean.Fmt.fmtTryCatchFinally`
  - [`Lean.Parser.Term.doIdDecl`](src/Lean/Parser/Do.lean#L93), in `Lean.Fmt.fmtDoLetArrow`, `Lean.Fmt.fmtDoReassignArrow`, `Lean.Fmt.fmtWithDoIdDecl`
  - [`Lean.Parser.Term.doIfLetBind`](src/Lean/Parser/Do.lean#L166), in `Lean.Fmt.fmtDoIfLet`
  - [`Lean.Parser.Term.doIfLetPure`](src/Lean/Parser/Do.lean#L165), in `Lean.Fmt.fmtDoIfLet`
  - [`Lean.Parser.Term.doPatDecl`](src/Lean/Parser/Do.lean#L96), in `Lean.Fmt.fmtDoLetArrow`, `Lean.Fmt.fmtDoReassignArrow`, `Lean.Fmt.fmtWithDoPatDecl`
  - [`Lean.Parser.Term.doSeqItem`](src/Lean/Parser/Do.lean#L27), in `Lean.Fmt.fmtDoSeqBracketed`, `Lean.Fmt.fmtDoSeqIndent`, `Lean.Fmt.fmtDoSeqItems`
- [Lean.Parser.Syntax](src/Lean/Parser/Syntax.lean) (2):
  - [`Lean.Parser.Command.elabTail`](src/Lean/Parser/Syntax.lean#L126), in `Lean.Fmt.fmtElab`
  - [`Lean.Parser.Command.macroTail`](src/Lean/Parser/Syntax.lean#L118), in `Lean.Fmt.fmtMacro`
- [Lean.Parser.Term](src/Lean/Parser/Term.lean) (14):
  - [`Lean.Parser.Term.basicFun`](src/Lean/Parser/Term.lean#L507), in `Lean.Fmt.fmtFun`
  - [`Lean.Parser.Term.byTactic'`](src/Lean/Parser/Term.lean#L233), in `Lean.Fmt.fmtShow`, `Lean.Fmt.fmtSuffices`, `Lean.Fmt.fmtTacticSuffices`
  - [`Lean.Parser.Term.fromTerm`](src/Lean/Parser/Term.lean#L342), in `Lean.Fmt.fmtShow`, `Lean.Fmt.fmtSuffices`, `Lean.Fmt.fmtTacticSuffices`
  - [`Lean.Parser.Term.letRecDecl`](src/Lean/Parser/Term.lean#L837), in `Lean.Fmt.fmtFullLetRecDecl.isSimpleDecl`, `Lean.Fmt.fmtLetRecDecl`, `Lean.Fmt.fmtLetRecDecls` +2
  - [`Lean.Parser.Term.letRecDecls`](src/Lean/Parser/Term.lean#L841), in `Lean.Fmt.fmtDoLetRec`, `Lean.Fmt.fmtFullLetRecDecl`, `Lean.Fmt.fmtFullLetRecDecl.isSimpleDecl` +4
  - [`Lean.Parser.Term.local`](src/Lean/Parser/Term.lean#L708), in `Lean.Fmt.fmtAttrKind`
  - [`Lean.Parser.Term.macroDollarArg`](src/Lean/Parser/Term.lean#L1147), in `Lean.Fmt.fmtStateRefT`
  - [`Lean.Parser.Term.matchAlt`](src/Lean/Parser/Term.lean#L389), in `Lean.Fmt.fmtFun.isSingleMatchAlt`, `Lean.Fmt.fmtMatchAlt`, `Lean.Fmt.fmtMatchAlts` +1
  - [`Lean.Parser.Term.matchAltsWhereDecls`](src/Lean/Parser/Term.lean#L867), in `Lake.Formatters.fmtCacheServiceCommand`, `Lean.Fmt.fmtAbbrev`, `Lean.Fmt.fmtDefinition` +4
  - [`Lean.Parser.Term.matchExprAlt`](src/Lean/Parser/Term.lean#L1174), in `Lean.Fmt.fmtMatchExprAlt`
  - [`Lean.Parser.Term.matchExprElseAlt`](src/Lean/Parser/Term.lean#L1175), in `Lean.Fmt.fmtMatchExprElseAlt`
  - [`Lean.Parser.Term.scoped`](src/Lean/Parser/Term.lean#L707), in `Lean.Fmt.fmtAttrKind`
  - [`Lean.Parser.Term.sufficesDecl`](src/Lean/Parser/Term.lean#L345), in `Lean.Fmt.fmtSuffices`, `Lean.Fmt.fmtTacticSuffices`
  - [`Lean.Parser.Termination.decreasingBy`](src/Lean/Parser/Term.lean#L816), in `Lean.Fmt.fmtTerminationSuffix`
- [Lean.Parser.Term.Basic](src/Lean/Parser/Term/Basic.lean) (4):
  - [`Lean.Parser.Term.binderDefault`](src/Lean/Parser/Term/Basic.lean#L186), in `Lake.Formatters.fmtBracketedSimpleBinder`, `Lean.Fmt.BinderKind.classify`, `Lean.Fmt.fmtBinder` +12
  - [`Lean.Parser.Term.binderTactic`](src/Lean/Parser/Term/Basic.lean#L183), in `Lake.Formatters.fmtBracketedSimpleBinder`, `Lean.Fmt.BinderKind.classify`, `Lean.Fmt.fmtBinder` +12
  - [`Lean.Parser.Term.structInstFields`](src/Lean/Parser/Term/Basic.lean#L300), in `Lake.Formatters.fmtCacheServiceCommand`, `Lake.Formatters.fmtWithOptConfig`, `Lean.Fmt.fmtAbbrev` +6
  - [`Lean.Parser.Term.typeSpec`](src/Lean/Parser/Term/Basic.lean#L261), in `Lake.Formatters.fmtConfigDecl`, `Lake.Formatters.fmtConfigField`, `Lake.Formatters.fmtWithBuildDeclSig` +27
- [Lean.Widget.Commands](src/Lean/Widget/Commands.lean) (1):
  - [`Lean.Widget.widgetInstanceSpec`](src/Lean/Widget/Commands.lean#L21), in `Lean.Fmt.fmtAddWidgetSpec`, `Lean.Fmt.fmtWidgetCmd`
- [Std.Tactic.Do.Syntax](src/Std/Tactic/Do/Syntax.lean) (2):
  - [`Lean.Parser.Tactic.mrefinePats`](src/Std/Tactic/Do/Syntax.lean#L274), in `Lean.Fmt.fmtMRefinePatTuple`
  - [`Lean.Parser.Tactic.vcAlt`](src/Std/Tactic/Do/Syntax.lean#L391), in `Lean.Fmt.fmtVCAlt`, `Lean.Fmt.fmtVCAlts`
- [Std.WP.Tactic](src/Std/WP/Tactic.lean) (3):
  - [`Lean.Parser.Tactic.frameAlt`](src/Std/WP/Tactic.lean#L62), in `Lean.Fmt.fmtFrameAlt`, `Lean.Fmt.fmtGrindVCGen`, `Lean.Fmt.fmtVCGen`
  - [`Lean.Parser.Tactic.invariantCaseAlt`](src/Std/WP/Tactic.lean#L41), in `Lean.Fmt.fmtInvariantAlt`, `Lean.Fmt.fmtInvariantAlts`
  - [`Lean.Parser.Tactic.invariantDotAlt`](src/Std/WP/Tactic.lean#L36), in `Lean.Fmt.fmtInvariantAlt`, `Lean.Fmt.fmtInvariantAlts`

Generic kinds, which no parser declaration defines (`ident`, `group`, the `token.*` kinds of non-reserved symbols and others). They are not parsers of their own: `Lean.Doc.Parser.parseFailure`, `antiquotName`, `antiquotNestedExpr`, `group`, `ident`, `patternIgnore`, `token.all`, `token.check`, `token.disch`, `token.discharger`, `token.drop`, `token.elim`, `token.error`, `token.exact`, `token.false`, `token.info`, `token.lax`, `token.move`, `token.normalized`, `token.pass`, `token.sorted`, `token.squash`, `token.trace`, `token.true`, `token.warning`, `token.« := »`, `token.« <-»`, `token.« check»`, `token.« sym»`, `token.« where »`, `token.« ←»`, `token.«*»`, `token.«->»`, `token.«.»`, `token.«<-»`, `token.«<=»`, `token.«=>»`, `token.«invariants »`, `token.«invariants? »`, `token.«·»`, `token.«←»`, `token.«→»`, `token.«⇐»`, `token.«⇒»`, `token.«⊢»`

## Review history

No completed review yet.

<!-- fmt-review: generated, end. Free-form notes below this line are kept. -->
## Notes

