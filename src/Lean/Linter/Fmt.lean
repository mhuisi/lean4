/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Linter.Util
public import Lean.Elab.Command
import Lean.Fmt.FmtM

public section

namespace Lean.Linter

open Lean Elab.Command

register_builtin_option linter.missingFormatter : Bool := {
  defValue := false
  descr := "enable the 'missing formatter' linter"
}

register_builtin_option linter.missingFormatter.ignorePrivate : Bool := {
  defValue := false
  descr := "make the 'missing formatter' linter ignore syntax with a private node kind, which is \
    what `local syntax`, `local macro` and `local notation` produce"
}

/-- The syntax an error refers to, falling back to the whole command. -/
private def errorRef (cmdStx : Syntax) : Fmt.Error → Syntax
  | .emptyInputSyntax stx ..
  | .formattingFailure stx ..
  | .taintedFormatting stx ..
  | .malformedInputSyntax stx ..
  | .ambiguousChoiceNode stx ..
  | .headerError stx .. => stx
  | _ => cmdStx

/-- Whether `kind` is exempt from being reported. A private kind stems from a `local` syntax
declaration, whose mangled kind no formatter can name. -/
private def isIgnoredKind (opts : Options) (kind : Name) : Bool :=
  kind == nullKind || (linter.missingFormatter.ignorePrivate.get opts && isPrivateName kind)

/-- The slice of `text` covered by `stx`, extended to whole lines.
`Fmt.collectSyntaxLineInfos'` reads the line information off this slice, so it must begin at a line
boundary for the indentation and length of the first line to be accurate. -/
private def sourceSliceOfSyntax (text : FileMap) (stx : Syntax) : String.Slice :=
  let source := text.source.toSlice
  match stx.getStartPos? with
  | none => source
  | some startPos =>
    let endPos := (stx.getTrailingTailPos? <|> stx.getTailPos?).getD startPos
    let sliceStartPos := text.lineStart (text.toPosition startPos).line
    let sliceEndPos := text.lineStart ((text.toPosition endPos).line + 1)
    source.subslice! (source.pos! sliceStartPos) (source.pos! sliceEndPos) |>.toSlice

private def checkMissingFormatter (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let text ← getFileMap
  let opts ← getOptions
  let lineInfos := Fmt.collectSyntaxLineInfos' (sourceSliceOfSyntax text stx) stx
  let ctx := {
    env
    text
    initialSnap? := none
    opts
    lineInfos
  }
  -- An aborting error hides all missing formatters of the command, so it is reported as well.
  let r ← match FmtM.run ctx (Fmt.fmt stx) with
    | .ok r => pure r
    | .error e =>
      logLint linter.missingFormatter (errorRef stx e) <|
        m!"The auto-formatter failed, so this command was not checked for missing formatters:\n\n" ++
        toString e
      return
  for (range, missingFormatter) in r.missingFormatters do
    if isIgnoredKind opts missingFormatter.kind then continue
    logLint linter.missingFormatter (.ofRange range)
      m!"no auto-formatter registered for syntax kind {Expr.const missingFormatter.kind []}"
  for (range, partialFormatter) in r.partialFormatters do
    let kind := partialFormatter.stx.getKind
    if isIgnoredKind opts kind then continue
    let fmtName :=
      if ! partialFormatter.formatterName.isAnonymous then
        m!"{Expr.const partialFormatter.formatterName []} "
      else
        m!""
    logLint linter.missingFormatter (.ofRange range) <|
      m!"Auto-formatter {fmtName}for syntax kind {Expr.const kind []} is incomplete.\n" ++
      m!"The syntax at the location has the following form:\n\n" ++
      toString partialFormatter.stx

/-- Linter that warns about syntax nodes for which no auto-formatter is registered.
The linter notes the `SyntaxNodeKind` in the warning message.

Set `linter.missingFormatter.ignorePrivate` to skip syntax declared with `local`. -/
def missingFormatter : Linter where
  run cmdStx := do
    unless linter.missingFormatter.get (← getLinterOptions).toOptions do
      return
    -- `missing` nodes from parser error recovery make formatters fail, which would be reported as
    -- spurious incomplete formatters. The formatter entry points reject such input as well.
    if cmdStx.hasMissing then
      return
    checkMissingFormatter cmdStx

builtin_initialize addLinter missingFormatter

end Lean.Linter
