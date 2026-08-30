---
name: fmt-formatters
description: Write formatters for the Lean auto-formatter Fmt. Use when adding or fixing a formatter for a syntax node kind (@[builtin_fmt]/@[builtin_infix_fmt]), working in src/Lean/Fmt/Formatters/, or composing formatting documents with Layouts.lean/Primitives.lean.
---

# Writing `Fmt` Formatters

`Fmt` is Lean's auto-formatter (`lake fmt`). Formatters live in
`src/Lean/Fmt/Formatters/` and translate `Syntax` into a formatting document
(`TaggedDoc`); an optimizing renderer then picks the best layout among the
alternatives the document offers. Key modules:

- `src/Lean/Fmt/FmtM/Basic.lean` — `fmt`, `fmt?`, `fmtArray`, `fmtSepArray`, `fmtRaw`, `fmtAtomic`, whitespace helpers
- `src/Lean/Fmt/FmtM/Layouts.lean` — reusable layouts (**prefer these**)
- `src/Lean/Fmt/FmtM/Primitives.lean` — low-level `TaggedDoc` primitives, `combine`, `stickyCombine`, `sticky`, `withPosition`
- `src/Lean/Fmt/FmtM/CommonFormatters.lean` — `fmtAppLike`, `fmtFixedApp`, `fmtProjLike`: the shared machinery for application- and projection-shaped syntax
- `src/Lean/Fmt/FmtM/Attribute.lean` — the `Fmt` types, the five registration attributes, and the `FmtProvider` dispatch mechanism
- `src/Lean/Fmt/Core/Basic.lean` — underlying `Doc` language with detailed doc comments
- `src/Lean/Fmt/Core/Formatter.lean` — the optimizer and the default cost function

**Where a new formatter goes:** `Formatters/` mirrors the source tree of the *parsers
being formatted*. A formatter for syntax defined in `src/Init/ByCases.lean` goes in
`src/Lean/Fmt/Formatters/Init/ByCases.lean` (creating that file + its aggregation-file
`public import`), **not** in whichever existing file holds similar formatters. Decide
placement from where the *syntax* is defined, not from what the formatter resembles. See
[module-structure.md](references/module-structure.md) for the full layout and module header.

For as-needed details, read:

- [locating-parsers.md](references/locating-parsers.md) — finding the parser for a piece of syntax; which parsers get their own syntax node kind
- [antiquotations.md](references/antiquotations.md) — writing the syntax match of a formatter, with subtleties
- [new-layouts.md](references/new-layouts.md) — criteria for proposing a new layout in `Layouts.lean`
- [module-structure.md](references/module-structure.md) — directory layout of `Formatters/`, aggregation files, module header template

## Examples

A simple formatter (`fmtExport`, `Formatters/Lean/Parser/Command.lean`): match all
components (including tokens, via `%$name`), recurse with `fmt`/`fmtArray`, assemble
with layouts:

```lean
@[builtin_fmt Lean.Parser.Command.export]
public def fmtExport : Fmt := fun
  | `(Parser.Command.export| export%$exportTk $namespaceId:ident (%$lbTk $exportedIds:ident* )%$rbTk ) => do
    let exportTk ← fmt exportTk
    let namespaceId ← fmt namespaceId
    let lbTk ← fmt lbTk
    let exportedIds ← fmtArray exportedIds
    let rbTk ← fmt rbTk
    let exportedIds := Layouts.fill exportedIds
    let exported := Layouts.parens lbTk exportedIds rbTk
    return Layouts.pseudoApplication #[exportTk, namespaceId, exported]
  | _ => throw .partialFormatter
```

Optional components and `keywordPrefixedSepFill` (`fmtDeriving`):

```lean
@[builtin_fmt Lean.Parser.Command.deriving]
public def fmtDeriving : Fmt
  | `(Parser.Command.deriving|
      deriving%$derivingTk $[noncomputable%$noncomputableTk?]? instance%$instanceTk $classes:derivingClass,* for%$forTk $terms:term,*) => do
    let derivingTk ← fmt derivingTk
    let noncomputableTk? ← fmt? noncomputableTk?
    let instanceTk ← fmt instanceTk
    let classes ← fmtTSepArray classes
    let forTk ← fmt forTk
    let terms ← fmtTSepArray terms
    let tks := Layouts.spacedAtomic #[derivingTk, noncomputableTk?, instanceTk]
    let lhs := Layouts.keywordPrefixedSepFill tks classes .nonSticky
    let «for» := Layouts.keywordPrefixedSepFill forTk terms .sticky
    return Layouts.pseudoApplication #[lhs, «for»]
  | _ => throw .partialFormatter
```

Multiple match alternatives and stickiness (`fmtFun`, `Formatters/Lean/Parser/Term.lean`):

```lean
@[builtin_fmt Lean.Parser.Term.fun]
public def fmtFun : Fmt := fun
  -- `fun%$funTk` also implicitly matches `λ` and `=>%$arrowTk` also matches `↦`.
  | `(Parser.Term.fun|
      fun%$funTk $binders:funBinder* $[ :%$typeAscriptionTk? $type? ]? =>%$arrowTk
        $body:term) => do
    let funTk ← fmt funTk
    let binders ← fmtArray binders
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let type? ← fmt? type?
    let arrowTk ← fmt arrowTk
    let body ← fmt body
    let signature := Layouts.localSignature .empty #[binders] typeAscriptionTk? type?
    return Layouts.assignmentDeclaration (sticky := true)
      (Layouts.spacedAtomic #[funTk, signature])
      arrowTk
      body
  -- `fun%$funTk` also implicitly matches `λ`.
  | `(Parser.Term.fun| fun%$funTk $matchAlts:matchAlts) => do
    let isSingleMatchAlt := isSingleMatchAlt matchAlts
    let funTk ← fmt funTk
    let matchAlts ← fmt matchAlts
    if isSingleMatchAlt then
      return maybeFlattened <| combine #[
        .withSepAfter funTk ⟨nl, nested⟩,
        matchAlts
      ]
    let doc := Layouts.matchDeclaration funTk matchAlts
    return sticky doc doc .coequal
  | _ => throw .partialFormatter
where
  isSingleMatchAlt : TSyntax ``Parser.Term.matchAlts → Bool
    | `(matchAlts| | $_ => $_) => true
    | _ => false
```

More good examples to read:

- `fmtGrindPattern` (`Formatters/Lean/Meta/Tactic/Grind/Parser.lean`) — a complex command composed entirely from layouts (`spacedAtomic`, `bracketed`, `application`, `sepFill`, `assignmentDeclaration`, `whereDeclaration`)
- `fmtStructInst` (`Formatters/Lean/Parser/Term.lean`) — `bracketed ... (.sparse nl)` for `{ ... }` blocks, sep arrays, `sepHorizontalOrVertical`
- `fmtAbbrev`/`fmtDefinition` (`Formatters/Lean/Parser/Command.lean`) — one alternative per declaration body form, delegating to `fmtAssignmentDeclaration`/`fmtMatchDeclaration`/`fmtWhereDeclaration`

## How formatters are structured

**Registration.** Five attributes register formatters, all keyed by syntax node kind
(declared in `FmtM/Attribute.lean`):

- `@[builtin_fmt <syntax node kind>]` on a `def ... : Fmt` — the general case.
- `@[builtin_infix_fmt <syntax node kind>]` on a `def ... : Fmt.InfixOperation`
  (`{ assoc := .left / .right / .middle, extendedChainKinds := #[...] }`) — for infix operators
  whose parsers do **not** have a `ParserDescr` (e.g. builtin `leading_parser`/`trailing_parser`
  definitions), and for those whose chains span several syntax node kinds. The attribute supplies
  the associativity and the extra chain kinds, and the generic `fmtInfixOperator` formats whole
  operator chains with them. Registering here rather than calling `fmtInfixOperator` from a plain
  `@[builtin_fmt]` is also what lets `Fmt` recognize the kind as an infix operation at all, which
  `infixOperatorCommentCollector` relies on to place comments around the operator.
- `@[builtin_conditional_fmt <syntax node kind>]` on a `def ... : ConditionalFmt`
  (`Syntax → FmtM (Option Fmt.Conditional)`) — for `if ... then ... else ...`-shaped syntax. The
  formatter only *deconstructs* one conditional into a `Conditional` record (`ifTk`, `cond`,
  `thenTk`, `thenBody`, `elseTk?`, `elseBody?`); the generic `fmtConditional` then walks the
  `else` branch, collapsing nested conditionals registered the same way into one `else if`
  chain, and hands the result to `Layouts.conditional`. Registering this instead of a plain
  `@[builtin_fmt]` is what makes `if/else if/else` chains lay out as a chain rather than as
  nested indented blocks (see `fmtIfThenElse`, `fmtIfLet`, `fmtTacIfThenElse`).
- `@[builtin_quantifier_fmt <syntax node kind>]` on a `def ... : QuantifierFmt`
  (`Syntax → Option Fmt.QuantifierComponents`) — for quantifier-shaped syntax (`∀`, `∃`, `Σ`,
  `∀ x > 0,` …). The formatter only *deconstructs* one quantifier into its head components
  (`quantifier`, `binders`, `typeAscriptionTk?`, `type?`, `commaTk`) plus the `body`; the generic
  `fmtQuantifier` then walks the body, collapsing every nested quantifier registered the same way
  into one chain, and hands the result to `Layouts.quantified`. Because the chain continues via
  this registry rather than via the deconstructor it started with, chains may span several
  quantifier kinds (`∀ ε > 0, ∃ δ > 0, ∀ x, p x` is one chain).
- `@[builtin_fmt_sticky_term]` on a `def ... : StickyTermFn` (a term predicate) — not a
  formatter but a predicate: it declares which head terms propagate their argument's stickiness
  out of an application, consulted by `fmtAppLike` via `propagatesRhsStickiness`. All registered
  functions are OR'd together, so each one only needs to recognize its own forms — e.g.
  `stickyIdRun` matches just `` `(Id.run) ``, which is what lets `Id.run do` keep the `do` block
  attached to the end of the line.

```lean
@[builtin_infix_fmt Lean.Parser.Syntax.addPrec]
public def fmtAddPrec : Fmt.InfixOperation := { assoc := .left }
```

**Dispatch goes through `FmtProvider`s, not through a hardcoded chain.** A `FmtProvider` maps
`Environment`/`Options`/`SyntaxNodeKind` to the formatter responsible for that kind (plus the
declaration name to blame for an incomplete formatter), or to `none` if it isn't responsible.
`getFormatterForKind?` is just `getFmtProviders env |>.findSome? …`; every mechanism above is a
provider registered with `addBuiltinFmtProvider <priority>` at the end of `FmtM/Basic.lean`, in
decreasing priority: choice nodes (1100), `@[builtin_fmt]` (1000), the specialized attributes
(800), `ParserDescr`-derived operators (600), `ParserDescr`-derived atomic syntax (400). Adding a
**new family** of formatters therefore means
declaring its attribute in `FmtM/Attribute.lean` (the `evalKey` boilerplate is shared —
`evalFmtAttributeKey`) and adding one `addBuiltinFmtProvider 800 <| keyedFmtProvider <attr> <driver>`
line; nothing in the dispatch function itself changes. `addBuiltinFmtProvider` is core-only;
packages downstream of core register a provider with `@[fmt_provider <priority>]` (default `1000`)
on a `meta def ... : FmtProvider`, which lands it in the same priority-ordered list.

**Notations with a `ParserDescr` need no attribute at all.** The low-priority providers derive a
formatter from the parser's shape when nothing else claims the kind: `infixl`/`infixr`/`notation`
operators get `fmtInfixOperator` with the associativity derived from the precedences, and
`prefix`/`postfix` notations (a `ParserDescr` of shape `symbol >> term:argPrec` resp. a
`TrailingParserDescr` of shape `symbol` at `lhsPrec == prec`) get `fmtPrefixOperator` /
`fmtPostfixOperator`. Only write a formatter for these when the derived one is wrong.

When a chain spans *several* node kinds, name them in `extendedChainKinds`, e.g. `fmtArrow`:

```lean
@[builtin_infix_fmt Lean.Parser.Term.arrow]
public def fmtArrow : Fmt.InfixOperation :=
  { assoc := .right, extendedChainKinds := #[``Parser.Term.depArrow] }
```

**1. Syntax match.** A formatter starts with a syntax match (an anti-quotation pattern)
that binds *every* component of the syntax to a name — including tokens, bound with
`%$name` (e.g. `export%$exportTk`). Names of components that can be absent/empty are
suffixed with a question mark (`$type?`, `typeAscriptionTk?`). When no alternative
matches (e.g. because the parser changed since the formatter was written), the formatter
throws a `.partialFormatter` exception: `fmt` then falls back to `fmtRaw`, which retains
the formatting of the input file, and records the incident so it can be reported. Every
formatter therefore ends with `| _ => throw .partialFormatter`.
See [antiquotations.md](references/antiquotations.md) for pattern subtleties.

**Always reach for an anti-quotation first; manually deconstructing the syntax
(`getStxArg!`, `stx[i]`, `.getArgs`) is a last resort.** An anti-quotation names the
parser and matches by structure, so it documents the shape and fails loudly (`partialFormatter`)
when the grammar changes. Index-based deconstruction is silent and fragile: it hard-codes
positions that drift when the parser gains an argument, and it is easy to read the wrong child.
Fall back to it *only* for the specific things the anti-quotation parser cannot express —
`patternIgnore` tokens, `linebreak`-guarded repetitions, "match any of several kinds",
quotation tokens (`` `( ``, backticks, `$`), dangling-dot completion syntax — and even then
keep the rest of the pattern an anti-quotation, deconstructing only the one part that needs it
(see the structural-fallback subtleties in [antiquotations.md](references/antiquotations.md)).
When you *do* deconstruct, read each child with an indexed `getStxArg! stx i` (it throws
`partialFormatter` on a missing/out-of-range child) rather than `stx.getArgs.mapM` — indexed
access fails loudly if the parser's arity changes instead of silently misformatting.

**2. Recursion.** For each component, recurse using `fmt` (single syntax), `fmt?`
(optional syntax → `empty` if absent), `fmtArray` (arrays), and `fmtSepArray`/`fmtTSepArray`
(separated arrays, keeping the separators), or one of the many `fmt*` utility functions
(e.g. `fmtDeclarationSignature`, see below). Parameterized formatters are invoked with the
`fmtWith` variants (`fmtWith`, `fmtWith?`, `fmtArrayWith`, `fmtTSepArrayWith`), which take
the formatter and its declaration name, e.g.
``fmtTSepArrayWith (fmtLetRecDecl compact) `fmtLetRecDecl decls`` (with a double-backquote
name literal in actual code).

The recursive call implicitly builds a mapping from the input syntax to the output
formatting document (via tags), along which information — notably comments — is
transferred to the output. **Never** reconstruct a component's text by hand; always go
through the recursion so this mapping stays intact.

**Bind each formatted document to the same name as its syntax variable** (shadowing it):
`let exportTk ← fmt exportTk`. Keep the `Tk` suffix on tokens; never introduce a `Doc`
suffix (`exportTk`, not `exportDoc`/`exportTkDoc`).

**3. Assembly.** Put the resulting documents back together into a single document using
layouts from `Layouts.lean` and, where genuinely necessary, primitives from
`Primitives.lean`.

**Recurse for every component first, then compose; do not interleave the two.** All the
`← fmt`/`fmt?`/`fmtArray` calls come first, the `Layouts.*` composition after. If you still
need a *raw* syntax node after recursing — e.g. the component array passed to
`fmtTermInstruction` is made of unformatted nodes — capture it *before* the `← fmt`
shadows the name:

```lean
| `(Parser.Term.dbgTrace| dbg_trace%$dbgTraceTk $arg ;%$semicolonTk $body:term) => do
    let components := #[dbgTraceTk, arg]   -- keep the raw syntax; `fmtTermInstruction` needs it
    let instruction := Layouts.pseudoApplication (← components.mapM fmt)
    fmtTermInstruction instruction components semicolonTk body
```

**Pass optional results straight into layouts; don't branch on presence.** `← fmt? x?` is
`empty` when the component is absent, and every layout (`combine`, `application`, `atomic`,
`infixOperator`, `prefixOperator`, …) drops `empty` components — and any dangling separators —
correctly. So prefer feeding the (possibly-`empty`) document into the layout over a manual
`match x? with | some _ => … | none => …`. For example, the optional `id@` of `matchExprPat`
is just `Layouts.atomic #[id?, atTk?, rhs]` (mirroring `fmtNamedPattern`), with
`id?`/`atTk?` from `fmt?`.

**Token-only parsers.** Formatters for parsers that only parse atoms can be just
`fmtAtomic` (i.e. `fmtRaw (isFallback := false)`):

```lean
@[builtin_fmt Lean.Parser.Command.private]
public def fmtPrivate : Fmt := fmtAtomic
```

Write one **only for builtin parsers** (`leading_parser` definitions of type `Parser`, as above)
and for syntax that is deliberately reproduced verbatim (quotations). Syntax declared with
`syntax`/`notation` needs no formatter at all when it only parses atoms: the lowest-priority
provider recognizes that from its `ParserDescr` and supplies `fmtAtomic` itself
(`derivedAtomicFmtProvider`, `hasAtomicFormatter`). Adding a redundant stub for such a kind is
noise.

## Prefer layouts over primitives

Layouts from `Layouts.lean` encode the formatting conventions of the Lean style and
handle empty documents, stickiness, and flattening correctly. **Always prefer a layout
from `Layouts.lean` over hand-rolling with primitives from `Primitives.lean`.**
Primitives are only for special formatting that is specific to one syntax and not
expressible as a composition of layouts. If you find yourself building the same
primitive composition in several formatters, propose a new layout instead
(see [new-layouts.md](references/new-layouts.md)).

## What each layout is for

For plain `Array TaggedDoc` (these are thin wrappers around the general `Layouts.array`
with a `Types.ArrayFormat` argument — `.join`, `.joinUsingSpace`, `.joinUsingBreak`,
`.joinUsingNl (allowFlattening)`, or `.fill`; `array` drops always-empty components and
passes a lone survivor through unchanged):

| Layout | Use for |
|---|---|
| `Layouts.atomic` | Components glued together with nothing in between, never broken apart (e.g. `declId` + universe annotation, prefix `-` + operand) |
| `Layouts.atomicInfixOperator` | `atomic`, but `nested` and passing a lone component through unchanged — glued operator chains like `xs[i]` |
| `Layouts.spacedAtomic` | Components joined by single spaces, never broken (runs of keywords: `private noncomputable def`) |
| `Layouts.fill` | Paragraph-style filling: put as many components on a line as fit, then break (long lists of identifiers) |
| `Layouts.horizontalOrVertical` | Either everything on one line separated by spaces, or every component on its own line — no in-between (attribute + decl, struct-inst body parts). `spacing := false` omits the spaces in the flat form (a plain break between components) |
| `Layouts.lines` | Every component on its own line, never flattened (constructor lists, fields, doc comment above decl) |
| `Layouts.spacedLines` | Every component on its own line with a blank line in between |

For separated arrays (`TaggedDoc.SepArray`, from `fmtSepArray`/`fmtTSepArray` — these
keep separator tokens like `,` as documents):

| Layout | Use for |
|---|---|
| `Layouts.sepFill` | Fill, with the separators attached to the elements (comma-separated lists: deriving classes, patterns) |
| `Layouts.sepLines` | One element per line; the required `includeSeps` argument chooses whether the separators stay at line ends (`let rec` declaration lists) or are dropped (tactic sequences) |
| `Layouts.sepHorizontalOrVertical` | All on one line or one per line (struct-inst `with`-sources); also takes a required `includeSeps` |

These are thin wrappers around the general `Layouts.sepArray`, whose
`Types.SepArrayFormat` argument is `.joinUsingSep afterElem? afterSep?`,
`.fillUsingSep afterElem? afterSep?`, or `.joinUsingNl allowFlattening afterElem?`; each
also takes a `trailingSep` mode
(`.excludeTrailingSep` — the default — `.includeTrailingSep`, or `.retainTrailingSep`).
It drops always-empty elements together with their separators. To append a trailing element
to a `SepArray` (e.g. the `..` ellipsis in struct instances), use `SepArray.pushElem`;
`SepArray.mapElems` maps over the elements without touching the separators, and
`SepArray.numElems` counts the elements.

Lean-specific layouts:

| Layout | Use for |
|---|---|
| `Layouts.retainedWhitespace` | Interleave documents with whitespace documents (from `fmtTrailingWithRetainedNewlines[AndComments]`) to preserve the user's blank lines/comments between parts of a declaration |
| `Layouts.prefixOperator` / `Layouts.postfixOperator` | `-x`, `@t`, `x⁻¹`; `.withSpacing`/`.withoutSpacing` chooses whether operator and operand are glued |
| `Layouts.infixOperator` | Alternating chain `#[operand, op, operand, ...]`. By default operators lead their line when broken (`:` at line start); `trailingOperator := true` breaks *after* operators instead. `.sparse` (default) only fills; `.dense` additionally offers a fallback where everything except the last operand is flattened (good for `:=`-like chains where only the rhs should break). Both formats also take `hardNestedFirstOperand` (indentation stacking, default `true`) and `spacing` (default `true`; `false` glues operators to their operands) |
| `Layouts.typeAscription` | The `lhs : rhs` triple — `infixOperator #[lhs, tk, rhs]` with `.dense` |
| `Layouts.pipeOperator` | Operator chains that break after the operator with dense fallback (`infixOperator … (.dense (trailingOperator := true))`) |
| `Layouts.keywordPrefixedSeq` | Keyword followed by one operand, breaking + nesting after the keyword (`namespace Foo`, `by tac`, `from e`); `.sticky` or `.nonSticky` |
| `Layouts.keywordPrefixedTerm` | Keyword glued to a single operand by a space, with proper sticky and empty handling — clause suffixes like `with pat`, `at h`, `hiding foo` (`.sticky`/`.nonSticky`). Unlike `keywordPrefixedSeq`, it never breaks between keyword and operand |
| `Layouts.keywordPrefixedSepArray` / `Layouts.keywordPrefixedSepFill` | Keyword followed by a separated list (`deriving Foo, Bar`, `for x, y`): list after the keyword, or on its own nested lines below it; `sepFill` fixes the list layout to `sepFill` (`.sticky`/`.nonSticky`) |
| `Layouts.keywordSeparated` | Two sides separated by a keyword that may either trail the lhs line or lead the rhs line (`show ... from ...`, `show ... by ...`, `match ... with ...`, `set_option ... in ...`). The `Types.KeywordSeparatedFormat` options are `allowFlattening` (forbid the single-line form with `false`) and `nestedRhs` (don't indent the rhs with `false`) |
| `Layouts.blocks` | A sequence of blocks joined by flattenable newlines with sticky attachment between adjacent blocks — chained tactic modifiers and clause suffixes (`simp only [...] at h ⊢`, `conv at h in ...`, signature + `extends`). `Types.BlocksFormat` has `hardNestedFirstBlock` and `nested`, both `true` |
| `Layouts.conditional` | `if cond then ... else ...`, with a chain of `else if` branches (`Array Types.ElseIf`). Each `then`/`else` block may trail its keyword's line or break below it. The trailing `allowFlattening : Bool` is required and positional; flattening to one line is offered only when it is `true` *and* there are no `else if` branches. Reached through `@[builtin_conditional_fmt]`/`fmtConditional`, which passes `allowFlattening := ! inputSpannedMultipleLines` — don't call it directly |
| `Layouts.application` | Real function application: fill arguments with spaces, nest when broken, and parenthesize arguments that need it. `format : Types.ApplicationFormat` is a structure — `hardNestedFirstTerm := true`, `sparse := false` (set it to `true` to suppress the glued two-term fallback), and the two fields with no default, `parenthesize` and `respectPseudoAlignment`. Most formatters get here via `fmtAppLike`/`fmtFixedApp` rather than calling it. `applicationWithSomeFilled` gives per-argument fill control |
| `Layouts.pseudoApplication` | **The common case**: keyword-plus-operands sequences that only *look* like application (`export ns (ids)`, `exact e`, `deriving ... for ...`). Same layout as `application` with everything defaulted off (`parenthesize := false`, `respectPseudoAlignment := false`), so no argument is ever parenthesized. Prefer this over `application` unless you are formatting an actual application node |
| `Layouts.bracketed` | Bracket-delimited content. `.dense` glues brackets to the body (`(...)`), with `spacing := true` for a space just inside instead; `.sparse sep` allows breaking after the opening and before the closing bracket with a sticky variant (`{ ... }`); `.sparse`'s further options are `unindentedRb` (keep the closing bracket unindented, default `true`) and `stickynessKind` (default `.preferSticky`) |
| `Layouts.tuple` | Brackets around a separated array: everything on one line if it fits, otherwise one field per line |
| `Layouts.parens` | `( body )` — the `bracketed … .dense` special case for parenthesized content (prefer this over `bracketed … .dense`; used by `binder`, level/prec parens, named-arg lists) |
| `Layouts.parenthesizedSeq` | A parenthesized sequence `( seq )` that may break after `(` and before `)` (`bracketed … (.sparse «break»)`; parenthesized tactic/conv sequences) |
| `Layouts.collection` | List/array literals `[…]`, `#[…]` — filled elements inside `bracketed … .sparse`; `Types.ArrayLitFormat` offers `spacing` (space/`nl` just inside the brackets, for `⟨ … ⟩`-style syntax) and `unindentedRb` |
| `Layouts.localSignature` / `Layouts.globalSignature` | `lval binders : type` — binder groups plus optional type ascription; `local` for term-level signatures (`fun`, quantifiers), `global` for declaration headers (`def foo ... : T`) |
| `Layouts.assignmentDeclaration` | `signature := body`; `sticky := true` additionally gives the result a sticky variant (used for `fun ... => body`) |
| `Layouts.matchDeclaration` | Signature followed by match alternatives on the lines below |
| `Layouts.whereDeclaration` | `signature where body` with the body always on the lines below |
| `Layouts.binder` | A single binder `(x y : T := default)` |
| `Layouts.letDecl` | The declaration head of a `let`/`have`-like term (keyword + config + decl); `Types.LetTermFormat.separateSignatureAndDecl` breaks between `keyword config` and the decl instead of spacing them. Attach the body with `fmtTermInstruction` (which applies `retainedWhitespace`) rather than calling this directly |
| `Layouts.alt` / `Layouts.alts` | Match alternatives: `alt subAlts arrowTk rhs` builds one alternative (a `Types.Alt` with flat and non-flat variants), `alts` lays out the list, each on its own line, wrapped in `withPosition`; `allowFlattenedAlts := true` also offers a collapsed form where every alt is flattened (used for simple matches) |
| `Layouts.quantified` | Chains of quantifier heads + body (`∀ x, ∃ y, p`); marks its result `pseudoAligned` |
| `Layouts.subtype` | Bracketed infix bodies like `{ x // p x }` — a dense, `pseudoAligned` operator triple inside the `Types.BracketFormat` you pass in |
| `Layouts.strLit` | A string literal with its optional interpolation prefix (`s!`, `f!`, or `empty` for a plain one): `atomic`, marked `mkSelfDelimited` so surrounding layouts treat it as one unit |

Most formatters reach the declaration/binder/quantifier layouts through the `fmt*`
utility functions below rather than calling them directly.

## `combine`, `stickyCombine`, `withPosition`, `sticky` in detail

These primitives carry most of the semantic weight; understand them before
writing anything non-trivial.

### `combine`

`combine (cs : Array TaggedDoc.Component)` is the workhorse for joining components that
may be empty. A `Component` is a document (`doc? : Option TaggedDoc`) with an optional
separator before and/or after (`Component.withSepBefore` / `Component.withSepAfter`; a
bare `Option TaggedDoc` coerces to a separator-less `Component`). A separator (`Sep`) is
itself a document plus an optional `wrap` function:
`.withSepAfter keywordTk ⟨nl, nested⟩` means "after the keyword comes a flattenable
newline, and everything from that separator onward is wrapped in `nested`".

Semantics:

- **Empty documents**: components whose document `isAlwaysEmpty` are dropped *together
  with their separators*, so separators never dangle next to an absent optional
  component. This is why you can pass `← fmt? foo?` results straight in.
- Adjacent separators are collapsed (a `sepAfter` is dropped when the next component has
  its own `sepBefore`), and the leading separator of the first and trailing separator of
  the last remaining component are dropped.
- **`combine` is stickiness-agnostic.** It neither reads nor produces sticky variants; a
  sticky component passed to it simply loses its sticky alternative. Use `stickyCombine`
  when the joined document should offer one.

### `stickyCombine`

`stickyCombine (lhs : TaggedDoc) (sep : Sep) (rhs : TaggedDoc) (allowFlattening := true)`
is the sticky-aware two-part join, and the one to reach for whenever a keyword/head is
followed by a body that might itself be sticky. It builds `combine #[.withSepAfter lhs sep, rhs]`
and, if `rhs` has a sticky variant, adds the alternative in which `sep` is replaced by a
plain `space` and `rhs` by its sticky variant (via `withStickyAlt` with `rhs`'s own
`StickynessKind`) — letting e.g. a `fun ... =>` start on the previous line with only its
body broken. Most layouts that attach a body to a head (`keywordPrefixedSeq`,
`keywordPrefixedTerm`, `assignmentDeclaration`, `whereDeclaration`, `keywordSeparated`,
`conditional`) are built on it.

### `withPosition`

`withPosition body` (an alias for `aligned`) sets the indentation level inside `body` to
the column at which `body` starts. It is **crucial for correctness**: many parsers wrap
syntax in `withPosition` and constrain continuation lines with `colGt`/`colGe` (tactic
sequences, do-blocks, match alternatives). Without a corresponding `Fmt.withPosition` in
the formatter, the optimizer may produce a layout in which continuation lines are
indented less than the parser requires, so the output would re-parse differently or not
at all. Whenever the parser you are formatting uses `withPosition`/`colGt`/`colGe`, wrap
the corresponding document in `withPosition` (see `fmtTacticSeq1Indented`,
`fmtMatchAlts`).

### `sticky`

A document is *sticky* when it may attach to the end of the preceding line while only
its body breaks — `fun`, `by`, `do`, `{ ...` behave like this:

```lean
xs.map fun x =>
  x + 1
```

`sticky nonStickyVariant stickyVariant (kind : StickynessKind)` attaches `stickyVariant`
(plus the kind) as metadata to `nonStickyVariant`. Parent combinators (`stickyCombine`,
`Layouts.applicationWithSomeFilled`, `Layouts.infixOperator`, `Layouts.blocks`, app
formatters via `propagatesRhsStickiness`) discover it with `getSticky?` /
`getStickynessKind?` and add the corresponding alternative via `withStickyAlt`. Use
`propagateStickyness inner f` to lift a sticky `inner` document through a wrapper `f`
(optionally overriding the kind), e.g. how `bracketed … .dense` keeps its body's
stickiness.

The three `StickynessKind`s decide how `withStickyAlt` weighs the two variants:

| Kind | Behavior |
|---|---|
| `.coequal` | Both variants compete on equal footing (`fun` with match alternatives, most keyword clauses) |
| `.preferSticky` | The parent demotes the non-sticky layout to a flattened form or an overflow-penalized fallback, so the sticky attachment wins whenever it fits (`by`, `{ ...`, collection literals) |
| `.preferUnsticky` | The reverse: the sticky variant is only a height-penalized fallback (dense `(...)` brackets) |

Contract: in the `stickyVariant`, the left-hand "sticky" side (the head up to and
including `=>`/the keyword) should be `flattened`, so the head itself never breaks when
glued to the previous line; the body after it may break. Whether the *whole* sticky
alternative is additionally `maybeFlattened` is up to the parent formatter — do not bake
`maybeFlattened` into the sticky variant itself (the non-sticky variant typically is the
`maybeFlattened` one). See `Layouts.keywordPrefixedSeq` and `Layouts.assignmentDeclaration
(sticky := true)` for the pattern.

## Primitives at a glance

From `Primitives.lean` (semantics documented in depth on `Doc` in `Core/Basic.lean`):

- `nl` — newline; flattens to a single space.
- `break` — newline; flattens to the empty string (use between components that are glued when on one line).
- `hardNl` — newline that can never be flattened; flattening it fails the alternative.
- `text s ref` — a tagged text node (monadic). Rarely needed directly; `fmt` on a token produces it.
- `empty` — the empty document, neutral element of `++`; dropped by `combine` and layouts.
- `space` — a single-space text node.
- `nested d` — indent continuation lines of `d` by 2, *non-cumulatively*: multiple `nested` on the same line indent only once. This is the default indentation combinator.
- `hardNested d` — indent by 2 *cumulatively*: stacks with other indentation introduced on the same line.
- `doublyNested d` — `hardNested (nested d)`: one cumulative plus one non-cumulative level, for content that must end up indented past a sibling `nested` block.
- `flattened d` — render `d` with all newlines flattened (`nl` → space, `break` → "", `hardNl` → failure).
- `maybeFlattened d` — `d` or `flattened d`, optimizer's choice; the classic "group" of other pretty-printers.
- `unflattenable d` — the dual of `flattened`: flattening `d` fails, so `d` keeps its breaks even inside a `flattened` parent.
- `unindented d (onlyNonCumulative : Bool)` — strip indentation inside `d` (all of it, or only the non-cumulative `nested` levels). Used to pull a closing bracket back to the opening bracket's column.
- `aligned d` / `withPosition d` — align continuation lines to `d`'s start column (see above).
- `oneOf ds` — choose among alternatives; the optimizer picks the best non-failing one (empty array = failure). Share common subdocuments referentially between alternatives instead of duplicating their construction. `either a b` is the two-argument version.
- `guarded assertion d` — admit `d` only when `assertion columnPos indentation nonCumulativeIndentation` holds, letting an alternative depend on the layout context it lands in (`Layouts.bracketed .sparse` uses it to reject a one-line form whose closing bracket would sit right of the opening one).
- `withFailureFallbackPenalty d` / `withOverflowFallbackPenalty d` / `withHeightFallbackPenalty d` — add a penalty at one tier of the cost function (see the optimization criterion below), so `d` is chosen only if the alternatives are worse at that tier. `fallbackOnFailure d fallback`, `fallbackOnOverflow`, `fallbackOnHeight` are the `oneOf` shorthands.
- `final d` — forbid any text after `d` on the same line. `free d` — resolve `d` on its own and hide its width, height, and cost from the surrounding document (used for comments, which must not influence how the code around them breaks).
- `isAlwaysEmpty d` (also `isAlwaysNonEmpty`, `isAtomic`) — conservative check that `d` is guaranteed to render empty. Rarely needed in a formatter: layouts already drop empty components, so prefer passing the `empty` document through a layout (see step 3) over branching on this.
- `pseudoAligned d` — mark `d` as behaving like an `aligned` block without actually aligning it: layouts that would glue a dense/flattened-lhs fallback around their last operand (`infixOperator .dense`, `application` with `respectPseudoAlignment`) skip it for pseudo-aligned documents (they check `Layouts.permitDenseLayout`). Used by `Layouts.quantified` and `Layouts.subtype`.
- `mkSelfDelimited d (isBracketed := false)` — mark `d` as carrying its own delimiters (a literal, a projection chain, a bracketed body), read back with `isSelfDelimited`/`isBracketed`. `Layouts.application` uses it via `needsAppBrackets` to decide which arguments need parentheses, and `fmtAppLike` uses `isBracketed` to pick a sparse layout after a bracketed head.
- `mkRawFallback d` / `isRawFallback d` — mark a document produced by the `fmtRaw` fallback, so `fmtChoiceNode` can prefer an alternative that was actually formatted and `needsAppBrackets` can parenthesize it defensively.
- `pseudoDedented indentedVariant dedentedVariant` — carry a less-indented variant alongside a document. `fmtSeq` swaps it in when the document is the *last* element of a tactic sequence, so block-wrapping tactics (`classical tac`, `stop tac`, `unhygienic tac`) don't indent their body when nothing follows it.

## `fmt*` utility functions

Prefer these over re-deriving common shapes. From `FmtM/CommonFormatters.lean` — use these
whenever the syntax really is an application or a projection, rather than assembling
`Layouts.application` yourself:

- `fmtAppLike terms` — a full application `f a b c`: formats the head (unwrapping a projection head via `fmtProjLike`), formats the arguments with per-argument fill control, and propagates the last argument's stickiness out of the application when the head is registered with `@[builtin_fmt_sticky_term]`. This is what `fmtApp` is.
- `fmtFixedApp f args (format := …)` — the same argument handling for a head you have *already* formatted plus raw argument syntax, for keyword-headed syntax with a fixed arity. `fmtFixedApp'` additionally returns the formatted arguments.
- `fmtProjLike lhs dotTk field` — `lhs.field`, preserving `lhs`'s stickiness and marking the result self-delimited.
- `allowAppArgFill stx` — the predicate behind the above: a `fun` argument (bare, parenthesized, or as a named argument) must not be filled mid-line.

From `Formatters/Lean/Parser/Term/Basic.lean`, `.../Term.lean`, `.../Command.lean`:

- `fmtBinder lbTks lhses subBinders typeAscriptionTk? type? tacticOrDefault? rbTks` — any binder form: `(x y : T := v)`, `{x}`, `[inst]`, `⦃x⦄`, also unbracketed ones (empty `lbTks`/`rbTks`).
- `fmtBinders binders` — groups consecutive explicit/implicit binders and returns binder-group documents for `Layouts.localSignature`/`globalSignature`.
- `fmtLocalSignature`/`fmtGlobalSignature lval binders typeAscriptionTk? type?` — `lval binders : type` (`local` for term-level signatures, `global` for declaration headers).
- `fmtDeclarationSignature declTks namedPrio? declId? binders typeAscriptionTk? type?` — a full declaration header such as `def foo (x : Nat) : T`.
- `fmtAssignmentDeclaration declTk ... colonEqTk declBody terminationSuffix whereDecls?` — `sig := body` declarations plus termination suffix and `where` decls, retaining the user's blank lines between the parts.
- `fmtMatchDeclaration declTk ... matchAlts terminationSuffix whereDecls?` — declarations whose body is a list of match alternatives (`def f | 0 => ...`).
- `fmtWhereDeclaration declTk ... whereTk fields whereDecls?` — `sig where fields` declarations (e.g. `instance ... where`).
- `fmtStructureLike tk declId binders ... extends? sepTk? structCtor? structFields? optDeriving` — `structure`/`class` declarations.
- `fmtInductiveLike tks declId binders ... ctors computedFields? optDeriving` — `inductive`/`coinductive`/`class inductive` declarations.
- `fmtNamedArgumentTerm lbTk lhs colonEqTk body rbTk` — `(name := value)`-shaped syntax (named args, `(motive := ...)`, `(priority := ...)`).
- `fmtDeclWithAttributes attributes? decl (compact := false)` — places `@[...]` on the same line as the declaration when the attributes are simple, on their own line otherwise.
- `fmtLetRecDecls compact` — the declaration list of `let rec`.
- `fmtLetTerm keywordTk config? decl semicolonTk body` — `let`/`have` terms (`config?` optional), preserving comments and newlines after the declaration.
- `fmtTermInstruction instruction instructionComponents semicolonTk? body` — attaches a body to a `let`/`have`/`dbg_trace`-style instruction head (built with `Layouts.letDecl` or `Layouts.pseudoApplication`), retaining the user's blank lines/comments after the declaration. `instructionComponents` is the head's *raw* syntax (capture it before `← fmt` shadows the names); `semicolonTk?` is `none` for `do`-style instructions with no `;`. `fmtLetTerm`, `fmtLetrec`, and the `dbg_trace`/`idbg`-family formatters all go through this.

Also useful: `fmtDeclWithDeclModifiers` (a `declModifiers` node + decl; the underlying
`fmtDeclWithModifiers` takes doc comment, attributes, and modifier keywords separately),
`fmtSeq seq nestedKind?` (tactic/`do`/conv sequences: `withPosition`, one element per line
with a single-line alternative, plus `pseudoDedented` handling), `fmtArrayLit` (`[a, b, c]`),
and the whitespace-retaining helpers `fmt{Leading,Trailing}WithRetainedNewlines[AndComments]`,
`fmtArrayWithRetainedIntermediateNewlines[AndComments]` (and its `…With` and `…TSepArray…`
variants) for command-level syntax where the user's blank lines and comments must survive.

`fmtRawAsInSource` reproduces a node verbatim from the source instead of from its tokens.
It is a workaround for syntax whose tree does not faithfully represent the input (currently
Verso docstrings) and assumes the node contains no comments — do not reach for it as a
general escape hatch; `fmtAtomic`/`fmtRaw` are the normal ones.

## Formatters must be idempotent

Formatting already-formatted output must yield exactly the same output (a fixpoint).
The optimizer is deterministic, but formatters that consult the *input* layout (retained
newlines, raw fallbacks, line infos) can break idempotence if the first pass changes
what the second pass sees. Always verify by formatting twice (see Testing).

## The optimization criterion

You do not choose where lines break — you define the space of admissible layouts
(via `nl`/`maybeFlattened`/`oneOf`/layouts), and the optimizer picks the rendering that
is optimal under the cost function. `Fmt` uses `DefaultCost 100 200`: a soft width of 100
columns and an optimality cutoff width of 200. Its five components are compared
**lexicographically** (`DefaultCost.le` in `Core/Formatter.lean`):

1. `failureFallbackPenalty` — from `withFailureFallbackPenalty`,
2. `overflowCost` — the **sum of squared overflow** past the soft width, summed over lines,
3. `overflowFallbackPenalty` — from `withOverflowFallbackPenalty`,
4. `heightCost` — the number of newlines,
5. `heightFallbackPenalty` — from `withHeightFallbackPenalty`.

There is no last-line or break-position tie-breaker: among renderings with equal overflow
the optimizer simply minimizes line count, and anything finer has to be expressed with one
of the penalty tiers (which is what the `StickynessKind`s do).

Two consequences worth knowing: because overflow is *squared*, one line 10 columns over is
worse than five lines 4 columns over, so the optimizer spreads unavoidable overflow out
rather than concentrating it. And if *every* rendering of a document exceeds the cutoff
width of 200, the optimizer stops searching for the least-overflow rendering and picks
heuristically — which is the `taintedFormatting` error you get for very long unformatted
syntax (usually syntax with no formatter at all).

Practical consequence: offer alternatives generously (the optimizer handles the choice),
but share common subdocuments between alternatives rather than rebuilding them, so the
search stays efficient.

## Testing new formatters

1. Build stage1: `make -C build/release -j$(nproc)`.
2. Format an individual file with
   `./build/release/stage1/bin/lake fmt <path to file relative to repo root>`
   (formats in place; with no file argument it formats every module of the root package).
   **Elaboration errors do not block formatting** — only parse errors, header errors, and
   early-termination commands (`#exit`, a late `import`) do — so test files can freely use
   made-up names, unresolved identifiers, failing `assert_not_exists`, etc.
   But `lake fmt` *does* elaborate the whole file (it needs the final environment and options,
   e.g. to derive operator associativities), so the file's dependencies must be built first and
   anything that makes elaboration slow or non-terminating makes `lake fmt` hang. It elaborates
   with `Elab.inServer := true`, which is what makes a stray `idbg` in the file hang it.
3. For a new formatter `fmtFoo`, create a top-level test file in `tests/` named after
   the formatter: `tests/fmtFoo.lean`. It must contain many different examples of the
   syntax being formatted, chosen so the formatter is forced to break the examples in
   different places: forms that fit on one line, forms just over the 100-column soft
   width, deeply nested forms, forms with and without each optional component.
   **The test file must be human-readable** — a human uses it to evaluate the new
   formatter, so use meaningful names and realistic code, not generated noise.
4. Run the formatter **on a temporary copy**, never on the original test file — the
   original must stay untouched so the user can run the formatter on it himself and
   compare with a diff tool:

   ```bash
   scratch="${TMPDIR:-/tmp}"
   cp tests/fmtFoo.lean tests/fmtFoo.tmp.lean
   ./build/release/stage1/bin/lake fmt tests/fmtFoo.tmp.lean
   diff tests/fmtFoo.lean tests/fmtFoo.tmp.lean       # inspect the formatting
   cp tests/fmtFoo.tmp.lean "$scratch/fmtFoo.first.lean"
   ./build/release/stage1/bin/lake fmt tests/fmtFoo.tmp.lean
   diff "$scratch/fmtFoo.first.lean" tests/fmtFoo.tmp.lean  # must be empty (idempotence)
   rm tests/fmtFoo.tmp.lean
   ```
5. Validate the output by reading it: does every example break where a human would
   break it?

## Finding missing or incomplete formatters

To check which syntax in a file lacks a (complete) formatter without modifying the
file, run the `missingFormatter` linter via `lean` with the option set on the command
line:

```bash
./build/release/stage1/bin/lean -Dlinter.missingFormatter=true path/to/File.lean
```

This elaborates the file (no reformatting) and warns about every syntax node kind with
no registered auto-formatter, as well as every formatter that threw `.partialFormatter`
on the syntax at hand (including a dump of the unmatched syntax form).
