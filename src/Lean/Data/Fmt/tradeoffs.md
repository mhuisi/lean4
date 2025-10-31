# Comment-handling approaches in popular auto-formatters

Broadly, five distinct strategies are in wide use. They differ along two axes: (a) *when* comments get bound to syntactic positions (at parse time vs. at print time), and (b) *who* is responsible for emitting them (each per-node printer vs. a centralized mechanism).

## 1. Token-stream interleaving — gofmt, clang-format

Comments are kept in a stream parallel to the token/whitespace stream and re-interleaved during printing. In gofmt, comments are stored in `ast.File.Comments` (not attached to individual AST nodes); the printer merges the comment stream with the token and whitespace stream as it walks the tree. clang-format is more lexical still: tokens carry the whitespace preceding them, and comments are themselves tokens with "next/prev ignoring comments" helpers so the layout engine can reason about logical neighbors.

- Comments essentially stay where they were relative to surrounding tokens.
- The layout engine has to *work around* comments, which constrains reformatting (e.g. a line comment forces a break).
- Directive comments (`// clang-format off`) are easy because the formatter sees them in-stream.

## 2. AST attachment via heuristics — Prettier, Babel, Dart

At parse time, each comment is bound to an AST node and classified. Prettier uses two dimensions: *ownLine / endOfLine / remaining* (based on surrounding whitespace), then *leading / trailing / dangling* (relative to the chosen node), annotating each comment with `enclosingNode`, `precedingNode`, and `followingNode` so per-node printers can render them. Dart uses a simpler "comments precede a token" ownership model, where each token owns the comments before it in a doubly-linked list.

- Comments *move with their node* across refactors — great for big AST rewrites.
- Heuristics occasionally misattribute (Prettier ships `--debug-print-comments` precisely because of this).
- Dart's choice — comments attach to the *subsequent* token owned by the deepest subexpression — is known to force unwanted splits (tracked as `dart_style#1628`).

## 3. Explicit per-node comment handling — rustfmt, OCamlFormat

Every AST node's printer knows which comment positions are valid (before/after/inside) and emits them explicitly. rustfmt has a dedicated `src/comment.rs` with a `CommentRewrite` and `CommentCodeSlices` iterator; OCamlFormat lets the tree walker decide placement and will *refuse to emit output* rather than drop a comment.

- Highest precision: you can design rules per construct (e.g. doc-comment placement on `val` items in OCamlFormat).
- Huge implementation burden — you pay the cost in every single formatter.
- OCamlFormat's "refuse to format" gives a hard safety guarantee (no lost comments) at the expense of coverage.

## 4. Trivia on tokens — Roslyn (C#)

Every token carries leading and trailing `SyntaxTrivia` (whitespace, comments, directives). Reformatting replaces only the *whitespace* trivia; comment trivia is preserved in place because it's an immutable attribute of the token.

- Very robust: comments travel with their token through most edits.
- Reformatting the token *around* a comment is awkward — the comment pins structure.
- Related to the stream-of-tokens model in clang-format, but at AST-token granularity.

## 5. Format-then-reinsert — Lean Fmt

Format the document as if comments did not exist, then reinsert comments into the rendered text using the original token→comment association, falling back to moving the comment "outward" (e.g. from end-of-line to its own line, or before its containing line) when placement would violate a constraint.

---

## Evaluating Fmt against these

### Where Fmt wins

- **Formatter authors are insulated from comments.** This is the dominant advantage, and it compounds with Lean's design. Lean's surface language is both very large (tactics, commands, notation) and *user-extensible* — third parties write formatters for their own `syntax` declarations. rustfmt / OCamlFormat style (approach 3) would be a tax every extension author pays; Prettier-style heuristics (approach 2) centralize the problem but still require per-node `printComment` hooks in practice. Fmt pushes the problem into one place (`fmtWhitespace` + comment reinsertion) so new formatters compose without thinking about trivia. This is closer in spirit to Roslyn trivia (approach 4), but without even requiring the per-node printer to thread the trivia through.
- **Partial / failing formatters still get comments.** Because layout is chosen with no comment awareness, a formatter throwing `.partialFormatter` and falling back to `fmtRaw` doesn't risk losing or misplacing comments — they're added back uniformly in the post-pass. This matters a lot given the `fmtRaw` fallback is routinely used.
- **AI-generated / uncommented code is formatted the same way.** Approaches 1 and 4 make comments structural; their presence or absence can perturb layout. Fmt's layout is insensitive to comments, so the "no comments" case is simply a degenerate instance of the same algorithm.
- **Internal comment contents are untouched.** rustfmt, Black, and OCamlFormat all reflow or normalize comment bodies in some configurations, which bites when comments contain DSLs (Verso docstrings, doctests, etc.). Fmt sidesteps this by never touching comment internals.

### Where Fmt pays

- **Comment drift is a real user-visible cost.** Approaches 1 and 4 virtually never move a comment; Fmt can. A comment meaning "this specific argument is subtle" that ends up on the line above the call reads as attached to the *call*, not the argument — and the user has no easy mental model for when drift will happen. Prettier users hit the same class of complaint (`prettier#4398`), but there the movement is a consequence of AST attachment, which at least has a clear rule. In Fmt the rule is "best-effort reinsertion," which is harder to predict.
- **No safety net for "comment would be lost."** OCamlFormat refuses to emit output rather than drop a comment. Fmt could lose a comment to a bug in reinsertion without tripping an invariant, since the formatter never observed the comment to begin with. Consider whether reinsertion should assert every input comment reappears in the output.
- **Directive comments are harder to support.** `# fmt: off/on` (Black), `// clang-format off` (clang-format), `#[rustfmt::skip]` (rustfmt) rely on the formatter *seeing* comments in context. In Fmt, the formatter is blind to them, so a directive like "don't reformat this block" would need out-of-band plumbing — likely a pre-pass that carves out ranges before `fmt` runs.
- **Layout can't react to comments.** In Dart / gofmt, a trailing line comment near a call naturally forces a split; callers who add comments to document line-by-line choices get their layout preserved. Fmt picks the layout first and then finds a place for the comment, so a user who *intends* comment-driven splitting has no lever.

### Summary

Fmt sits at one extreme of a spectrum: it maximally decouples layout from comments in exchange for possible comment drift. That is probably the right trade for Lean specifically — the combination of extensible syntax, AI-generated code, comment-embedded DSLs, and the `partialFormatter` fallback all push in the same direction. The two concrete risks worth actively designing against are (i) loss-safety (assert no comment disappears in reinsertion), and (ii) a story for directive comments before users invent ad-hoc conventions.

## Sources

- [Prettier: What should the AST.comments field contain?](https://github.com/prettier/prettier/discussions/14158)
- [Prettier changes block comment node location in AST (issue #4398)](https://github.com/prettier/prettier/issues/4398)
- [gofmt talk — The Cultural Evolution of gofmt](https://go.dev/talks/2015/gofmt-en.slide)
- [Go `go/format` package](https://pkg.go.dev/go/format)
- [rustfmt `src/comment.rs`](https://github.com/rust-lang/rustfmt/blob/main/src/comment.rs)
- [rustfmt: Comments and Documentation (DeepWiki)](https://deepwiki.com/rust-lang/rustfmt/4.8-comments-and-documentation)
- [clang::format::FormatToken reference](https://clang.llvm.org/doxygen/structclang_1_1format_1_1FormatToken.html)
- [clang::format::BreakableToken reference](https://clang.llvm.org/doxygen/classclang_1_1format_1_1BreakableToken.html)
- [dart_style wiki — Formatting Rules](https://github.com/dart-lang/dart_style/wiki/Formatting-Rules)
- [dart_style issue #1628 — block-comment attachment to subsequent token](https://github.com/dart-lang/dart_style/issues/1628)
- [OCamlFormat repository](https://github.com/ocaml-ppx/ocamlformat)
- [Black code style — "Black might move comments around"](https://black.readthedocs.io/en/stable/the_black_code_style/current_style.html)
- [Roslyn SyntaxTrivia — NormalizeWhitespace](https://learn.microsoft.com/en-us/dotnet/api/microsoft.codeanalysis.csharp.syntaxextensions.normalizewhitespace)
- [Roslyn issue #24827 — NormalizeWhitespace preserving line feeds](https://github.com/dotnet/roslyn/issues/24827)
