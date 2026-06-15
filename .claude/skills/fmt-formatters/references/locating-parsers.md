# Locating Parsers and Their Syntax Node Kinds

## Finding the parser for a piece of syntax

The syntax node kind passed to `@[builtin_fmt <kind>]` is the full declaration name of
the parser (e.g. `Lean.Parser.Command.export`). To find it:

1. **Search by parser name** if you can guess it:

   ```bash
   grep -rn "def export" src/Lean/Parser/Command.lean
   grep -rn "def structInst\b" src/Lean/Parser/
   ```

2. **Search by a specific token** that occurs in the syntax. Tokens appear as string
   literals in parser definitions, usually with a leading and/or trailing space
   (the space encodes pretty-printer spacing):

   ```bash
   grep -rn '"export "' src/Lean/Parser/
   grep -rn '" deriving"' src/Lean/Parser/
   grep -rn '"grind_pattern"' src/Lean/
   ```

   If a literal search fails, try without the spaces, or search for a rarer token of
   the same syntax (e.g. `=/=` instead of `where`).

Main parser locations:

- `src/Lean/Parser/{Command,Term,Do,Tactic,Attr,Level,Extra,Module}.lean` — core grammar
- `src/Lean/Parser/Term/Basic.lean` etc. — submodules
- `src/Lean/Meta/Tactic/Grind/Parser.lean` — grind-related commands
- `syntax`/`notation`/`macro` declarations elsewhere in `src/` for non-builtin syntax

The kind of a syntax node can also be inspected directly: elaborate an example with
`#check` on a quotation, or `run_cmd` printing `stx.getKind` — but reading the parser
definition is usually faster and you will need it for the match pattern anyway.

For `syntax (name := k)`/`leading_parser` definitions the kind is the declared name, but
`macro`/`notation`/anonymous `syntax` get mangled auto-generated kinds you cannot guess
(`«term∃_,_»`, `«term_×__1»`, `tacticFunext___`, `Lean.«command__Unif_hint____Where_|_-⊢__»`).
For these, printing the kind is the reliable way to get the exact `@[builtin_fmt ...]`
argument — build the syntax in the right category:

```lean
run_cmd Lean.logInfo (toString (← `(tactic| funext x)).raw.getKind)
run_cmd Lean.logInfo (toString (← `(term| (x : Nat) × Nat)).raw.getKind)
```

Caveats when discovering kinds this way:

- **`macro (name := X) "tok" …` has kind `X`** (the declared `name`), *not* a token-derived
  mangled name. So the placeholder `macro (name := mclearMacro) "mclear"` has kind
  `…Tactic.mclearMacro`, even though a *bare* `macro "exfalso"` (no `name`) mangles to
  `…Tactic.tacticExfalso`.
- **`@[builtin_fmt KIND]` validates `KIND` at compile time** — an unknown kind is a hard build
  error (`Invalid [fmt] argument: Unknown syntax kind …`), so a wrong guess fails loudly rather
  than silently never firing. Lean on the build. The one exception: `KIND` is validated against
  the **stage0** compiler's environment (stage1's stdlib is compiled by `stage0/bin/lean`), so a
  formatter for a node kind whose *registration* you are adding in the same change — a fresh
  `registerBuiltinNodeKind` or `[builtin*Parser]` — fails validation until the registration
  reaches stage0. Land it in two steps: add the registration with the attribute commented out,
  `make update-stage0`, then uncomment and build.
- **Root-namespace kinds are written bare**, e.g. `@[builtin_fmt «term‹_›»]`,
  `@[builtin_fmt tacticGet_elem_tactic]` (syntax declared outside any `namespace`, like the tail of
  `Init/Tactics.lean`). Do **not** prefix them with `_root_.` — the attribute keeps the prefix
  literally and rejects it.

## Which parsers receive their own syntax node kind

Formatters are registered per syntax node kind, so only parsers that produce their own
node can carry their own formatter. Everything else is matched *inside* the parent
formatter's anti-quotation.

Parsers that **do** get their own kind:

- `leading_parser` / `trailing_parser` definitions — the kind is the full declaration
  name (`Lean.Parser.Command.export`).
- Parsers that explicitly wrap in `node k p` / `withKind`.
- `syntax (name := k) ... : cat`, `notation`, `infixl`/`infixr`/`prefix`/`postfix`,
  `macro` declarations — these produce `ParserDescr`s with (possibly auto-generated)
  kinds. Note: `infixl`/`infixr`/`prefix`/`postfix` notations with a `ParserDescr` get an
  infix/prefix/postfix formatter automatically (associativity is derived from the
  precedences); no attribute needed, and no formatter unless the derived one is wrong.

Parsers that do **not** get their own kind:

- Combinators: `optional (...)` produces a null node (match with `$[...]?`),
  `many`/`many1` produce null nodes (match with `$xs*`), `sepBy`/`sepBy1` produce null
  nodes with interleaved separators (match with `$xs,*`).
- Token parsers: `symbol`/string literals produce atoms; `ident`, `num`, `str`, `name`
  produce token nodes with the builtin kinds `` `ident ``, `` `num ``, ... (these
  builtin kinds *can* carry formatters, e.g. `@[builtin_fmt num] ... := fmtRaw`).
- Plain `def p := p₁ <|> p₂` without `node` — no kind of its own; register formatters
  for the kinds of the alternatives instead.
- Parser *categories* (`categoryParser`) — the parsed alternative determines the node.
  A category reference inside a parent parser (e.g. `structInstFieldDecl`) shows up as
  a child node of whatever kind was parsed; the parent formatter just recurses on it
  with `fmt`.

Consequence for formatter structure: a parser definition like

```lean
def optDeclSig := leading_parser many binder >> optional (" : " >> termParser)
```

has its own kind (`optDeclSig`), but the `many`/`optional` parts inside it do not —
your formatter for the *parent* matches them structurally with `$binders*` and
`$[:%$tk $type?:term]?`.
