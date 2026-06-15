# Formatter Module Structure

## Directory layout

`src/Lean/Fmt/Formatters/` mirrors the structure of the modules that contain the
syntax/parsers being formatted:

| Parsers defined in | Formatters live in |
|---|---|
| `Init.Notation` (`src/Init/Notation.lean`) | `src/Lean/Fmt/Formatters/Init/Notation.lean` |
| `Lean.Parser.Command` (`src/Lean/Parser/Command.lean`) | `src/Lean/Fmt/Formatters/Lean/Parser/Command.lean` |
| `Lean.Parser.Term.Basic` | `src/Lean/Fmt/Formatters/Lean/Parser/Term/Basic.lean` |
| `Lean.Meta.Tactic.Grind.Parser` | `src/Lean/Fmt/Formatters/Lean/Meta/Tactic/Grind/Parser.lean` |

Formatter modules are registered in aggregation files that mirror the hierarchy:

- `src/Lean/Fmt/Formatters.lean` publicly imports `Lean.Fmt.Formatters.Init` and
  `Lean.Fmt.Formatters.Lean`
- `src/Lean/Fmt/Formatters/Init.lean` publicly imports each
  `Lean.Fmt.Formatters.Init.*` module (e.g. `...Init.Notation`, `...Init.Tactics`)
- `src/Lean/Fmt/Formatters/Lean.lean` publicly imports `Lean.Fmt.Formatters.Lean.Meta`
  and `Lean.Fmt.Formatters.Lean.Parser`
- `src/Lean/Fmt/Formatters/Lean/Parser.lean` publicly imports each
  `Lean.Fmt.Formatters.Lean.Parser.*` module
- `src/Lean/Fmt/Formatters/Lean/Meta.lean` → `...Meta.Tactic` → `...Tactic.Grind` → etc.

**When adding a new formatter module, add a `public import` for it to the appropriate
aggregation file** (creating intermediate aggregation files if the path is new),
otherwise the formatters are never registered.

## Module header

New formatter modules use this header (get the year with `date +%Y`; author per repo
conventions):

```lean
/-
Copyright (c) <year> Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import <module of parser that formatters are for>
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

<formatters>
```

Notes:

- The `meta import` of the parser module is what makes the quotation patterns
  (`` `(Parser.Command.export| ...) ``) work — import the module that *defines* the
  parsers being formatted (e.g. `meta import Lean.Parser.Command`).
- These are `prelude` modules: nothing is auto-imported. Add `import Init.*` modules
  for stdlib features as needed (e.g. `import Init.While` for `while`/`repeat`,
  `import Init.Data` for common data structures).
- `import Lean.Fmt.FmtM.CommonFormatters` for `fmtAppLike`/`fmtFixedApp`/`fmtProjLike`;
  nearly every module that formats application-shaped syntax needs it.
- Import other formatter modules you build on (e.g.
  `public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic` for `fmtBinder`).
- Formatter definitions are `public def`; formatters referenced by name in `fmtWith`
  calls from other modules must be `public` as well.
- Every `Formatters/**` module shares `namespace Lean.Fmt` and they are all imported together,
  so each formatter `def` name must be **globally unique across the whole tree** — a duplicate is
  an "already declared" error. When a base name is already taken by another category's formatter
  (`fmtSorry`, `fmtSubst`, `fmtNofun`, `fmtShow`, … already exist for terms), disambiguate the new
  one, e.g. `fmtTacticSubst`, `fmtTacticShow`. Two formatters must also never register the *same*
  syntax-node kind; `@[builtin_fmt]` will not stop you, but only one wins.
- Do not add `/-! … -/` section docstrings to group formatters within a module —
  formatters are listed one after another without section headers.
