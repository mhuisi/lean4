---
name: fmt-review
description: Do the periodic post-hoc review of the parser and formatter changes in Lean core `master` since the last review, and keep `fmt-review.md` up to date. Use when the user asks to refresh, update or do the formatter review ("fmt review"), to find the parsers or formatters that changed since the last review, to record review verdicts, to complete a review, or to list the syntax that has no formatter.
---

# Post-hoc review of parser and formatter changes

## Background

Core developers change parsers without a review by the owner of the auto-formatter (the user):

- If a parser change breaks a formatter at compile time, the developer fixes the formatter. For
  example, an antiquotation in the formatter no longer matches the parser.
- If the change compiles, the formatter can break silently. A formatter that does not match the
  syntax throws `.partialFormatter`, and the output keeps the input layout of the syntax.

The user reviews these changes periodically with an agent and makes post-hoc fixes. This skill
gives the procedure. For the formatter code itself, load the `fmt-formatters` skill.

## Files and terms

| Path | Content |
|---|---|
| `fmt-review.md` | The tracking document. The tool writes the part between the two markers. Free-form notes go below the end marker. |
| `fmt-review.json` | The state: reference, target, items with verdicts, syntax without a formatter, notes, review history. |
| `fmt-review-inventory.json` | The inventory of the reference. Generated. Do not edit it. |
| `.claude/skills/fmt-review/scripts/fmt_review.py` | The tool. `--help` lists the commands. |
| `.claude/skills/fmt-review/scripts/inventory.lean` | Writes the inventory of a build. The tool runs it. |
| `.claude/skills/fmt-review/scripts/test_fmt_review.py` | Unit tests of the tool. |
| `build/fmt-review/` | The inventory of the current build and the lint logs. jj does not track it. |

- **Reference**: the `master` commit of the last completed review.
- **Target**: the `master` commit that the current build contains, normally `master`.
- **Inventory**: the syntax data of a build. It contains each parser declaration (type `Parser`,
  `TrailingParser`, `ParserFn`, `ParserDescr` or `TrailingParserDescr`) with a hash of its
  elaborated definition. It also contains each syntax node kind with the formatter that `Lean.Fmt`
  finds for it, the hash of each formatter declaration, the syntax categories and the tokens.
- **Item**: one difference between the reference inventory and the target inventory, or one
  commit that changes formatter files. Each item has a status.

In the commands that follow, `$T` is `python3 .claude/skills/fmt-review/scripts/fmt_review.py`.
Run all commands from the workspace root.

## Workspace and jj layout

- The workspace is `~/dev/lean4/fmt-review`. The bookmark `fmt-review` points to the commit with
  the state of the last completed review.
- The stack is: `master` → local fix changes (if there are any) → review commits → `@`.
- `master` tracks the remote `upstream`. The remote `origin` is the fork of the user.
- Do not push. The user pushes bookmarks. Never push to `master`.

## Item types

| Type | Meaning | What to examine |
|---|---|---|
| `syntax-changed` | The definition of a parser that defines syntax node kinds changed. | Compare the diff with the antiquotation patterns of the formatter: order and number of children, optional parts, tokens, alternatives. |
| `syntax-added` | New syntax. **no formatter** in the table means that it has none. | Decide if it needs a formatter now. If the syntax is not stable yet, defer the item or add a note to the missing list. |
| `syntax-removed` | The syntax no longer exists. | Make sure that its formatter and its examples in `tests/fmt` are gone. |
| `combinator-changed` | A parser without a kind of its own changed, for example `optConfig`. The item lists the kinds that use it. | Examine if the node shape of these kinds changed. A change that only adds `pp*` hints does not change parsing. |
| `kind-added`, `kind-removed` | A generic kind that no declaration defines appeared or disappeared. | These are rare. |
| `category-added`, `category-removed`, `category-changed` | A syntax category changed. | A new category needs formatters for its syntax and for its quotation kind `<category>.quot`. |
| `tokens` | Tokens were added to or removed from the token table. | A new token can make the output lex differently, for example two tokens without a space. |
| `fmt-changed` | The definition of a formatter that an attribute registers changed. | Review the diff: layouts, style, idempotence. |
| `fmt-added`, `fmt-replaced`, `fmt-removed` | A kind got a formatter, got a different formatter, or lost its formatter. | Review the formatter. |
| `commit` | A commit that changes formatter files: `src/Lean/Fmt`, `src/lake/Lake/Formatters`, `tests/fmt`, the formatter linter, scripts and skill. | Review the full diff: `jj diff --git -r <commit>`. |
| `fmt-incomplete` | `lint` found syntax in core for which the formatter threw `.partialFormatter`. | A fix is usually necessary. |
| `fmt-failure` | `lint` found a command for which the formatter failed. | A fix is usually necessary. |

"(source unchanged)" after an item id means that the text of the declaration did not change, but
its elaborated definition did. A declaration or an instance that it uses changed. Such an item is
usually `ok`.

| Status | Meaning |
|---|---|
| `pending` | Not reviewed. |
| `fix` | A fix is necessary and is not done. |
| `fixed` | The fix is done. The note names the change or the PR. |
| `ok` | Reviewed. Nothing to do. |
| `deferred` | Accepted for now. The item is carried into the next review. |

`pending` and `fix` are open. If an item changes after its verdict, the next refresh sets it back
to `pending`.

## Procedure 1: Refresh for the latest master

1. Fetch the remote: `jj git fetch --remote upstream`.
2. Rebase the stack: `jj rebase -b @ -d master`.
3. If a local fix change landed in `master`, abandon the local change: `jj abandon <change>`.
4. Build Lean in one memory-capped scope. Run no other heavy job at the same time:

   ```bash
   systemd-run --user --scope -q -p MemoryMax=30G -p MemorySwapMax=0 make -C build/release -j24
   ```

5. Refresh the items: `$T refresh`. It takes approximately 10 seconds.
6. Lint the core files that changed since the reference: `$T lint`. It runs
   `script/missing-fmts.sh` with 16 jobs in a 30G scope. It finds formatters that broke silently.
7. Run the formatter tests:

   ```bash
   CTEST_PARALLEL_LEVEL=16 CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test ARGS="-R '^fmt/'"
   ```

8. Give the user a report: the summary of `$T status`, the open items, the new syntax without a
   formatter, the lint results and the test results.

## Procedure 2: Review the items with the user

Go through the open items in the order of `fmt-review.md`. Do these steps for each item:

1. Show the details: `$T show <id>`. An id can also be a unique substring or a glob. The output
   gives the source diff since the reference, the kinds, the commits with PR links, and the source
   of the formatters.
2. Tell the user what changed, which formatters it affects, the PR, and your assessment.
3. If it is necessary, format an example. Write a small `.lean` file in a scratch directory and
   format it. For Lake syntax, add `--plugin=build/release/stage1/lib/lean/libLake_shared.so`:

   ```bash
   build/release/stage1/bin/lean -Dlinter.all=false --run tests/fmt/run_test.lean <file>
   build/release/stage1/bin/lean -Dlinter.fmt.missing=true <file>
   ```

   The first command prints the formatted file. The second command shows syntax without a
   formatter and incomplete formatters.
4. Propose a verdict. The user decides. The user can decide for several items at the same time.
5. Record the verdict: `$T verdict <id> --status ok --note "<reason>"`. Several ids and globs are
   permitted, for example `$T verdict 'commit:*' --status ok`.

## Procedure 3: Fix a formatter

1. Record the item: `$T verdict <id> --status fix --note "<what is wrong>"`.
2. Load the `fmt-formatters` skill. Make the fix in `@`, and add examples to `tests/fmt`.
3. Build Lean, and run the formatter tests.
4. Commit only the source files: `jj commit -m "fix: <subject>" src tests`. The state files stay
   in the new `@`.
5. Move the fix below the review commits: `jj rebase -r <fix change> -B 'roots(master..@)'`.
6. Create a bookmark for the PR: `jj bookmark create fmt-fix-<topic> -r <fix change>`. Tell the
   user that the bookmark is ready to push. The PR text follows `.claude/CLAUDE.md`.
7. Record the result: `$T verdict <id> --status fixed --note "change <change id>, fmt-fix-<topic>"`.
8. Refresh: `$T refresh`. The fix gives new `fmt-*` and `commit` items. Review them as usual.

## Procedure 4: Complete the review

1. Make sure that no item is open: `$T list --open`.
2. Make the target the new reference: `$T advance --summary "<one line>"`.
   - The tool makes the inventory again. It stops if the build is stale or if items are open.
   - It also stops if the build contains local changes. If these are fixes that will land in
     `master`, add `--allow-local`. Their syntax and formatters become part of the reference, and
     their commit items do not come back. When they land, their `commit` item starts as `ok`.
   - Use `--force` only if the user wants to carry open items into the next review.
   - `deferred` items are carried into the next review.
3. Commit the state: `jj commit -m "chore: fmt review up to <short target commit>"`.
4. Move the bookmark: `jj bookmark set fmt-review -r @-`.
5. Tell the user that they can push the bookmark: `jj git push --remote origin -b fmt-review`.

## Syntax without a formatter

`fmt-review.md` lists the syntax node kinds that have no formatter, grouped by module. The list
leaves out the private kinds of `local` syntax, which cannot have a formatter. It also leaves out
the generic kinds that no parser declaration defines, for example `ident`, `group` and `token.*`.
The list has two parts:

- **Not matched by a formatter**: no formatter code mentions the kind. These kinds need a
  formatter of their own.
- **Matched by the formatter of other syntax**: the code of another formatter mentions the kind,
  usually in an antiquotation pattern of the parent syntax. A quotation pattern compiles to
  `Syntax.isOfKind` checks with the kind name, so the inventory finds these names. Such a node
  only needs a formatter of its own if it also occurs outside of the parent syntax.

Commands:

- To list them: `$T missing`. Add `--module Lean.Parser` for one module prefix, `--unmatched`
  for the first part only, and `--all` to include the generic and exempt kinds.
- To add a note, for example "add a formatter when the syntax is stable":
  `$T missing-note <kind> --note "<text>"`.
- If a kind does not need a formatter of its own, mark it as exempt:
  `$T missing-note <kind> --exempt --note "<reason>"`. For example, the formatter of the parent
  syntax matches the node with an antiquotation and does not call `fmt` on it.
- After `$T lint`, the list also shows how often the linted files use each kind.

To add a formatter for a kind of the list, load the `fmt-formatters` skill.

## Limits of the detection

- The hashes are of elaborated definitions. A change in a declaration or instance that a parser
  uses can give an item with "(source unchanged)". Doc comments do not give items. `pp*` hints
  such as `ppSpace` give items.
- The tool finds parser changes only in declarations with a parser type. It does not find changes
  in helper functions of other types or in the C++ code. A change in a formatter helper, for
  example in `Layouts.lean`, gives only a `commit` item.
- Tokens of `scoped` syntax are not in the global token table, so `tokens` items do not show them.
- The tool links an item to commits with `jj file annotate` on the lines of the declaration.
  "(file)" in the table means that it used the commits that changed the file instead.
- After `advance --allow-local`, `show` compares with the source of the reference commit. This
  source does not contain the local changes.
- `lint` elaborates only the changed files. It finds incomplete formatters only for the syntax
  that these files use.

## Troubleshooting

- "source files are newer than their .olean files": build Lean first.
- "the target ... is not an ancestor of the working copy": rebase the stack (Procedure 1).
- `inventory.lean` does not compile: core changed an API that the script uses, for example
  `Parser.parserExtension`, `Parser.parserAliases2infoRef`, `Fmt.getFmtProviders` or
  `declRangeExt`. Fix the script. Then run the unit tests:
  `python3 .claude/skills/fmt-review/scripts/test_fmt_review.py`.
- If `fmt-review-inventory.json` becomes larger than 1 MiB, jj does not snapshot it. Then use
  `jj --config snapshot.max-new-file-size=4MiB status`.
- The commits of the formatter stack have divergent change ids in this repository. Use their
  commit ids.
