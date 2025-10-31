/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.ToString
public import Lean.Fmt.Core.Basic
public import Init.Data.Format.Syntax
public import Lean.Fmt.Core.Formatter

namespace Lean.Fmt

public inductive Error where
  | emptyInputSyntax
    (stx : Syntax)
    (msg : String := "Input syntax to the formatter is empty and contains only whitespace.")
  | partialFormatter
    (msg : String := s!"A formatter for is partial and does not handle the full syntax of the kind \
      it was registered for.")
  | formattingFailure
    (stx : Syntax)
    (msg : String := "Formatting of the document produced by the current set of `[fmt]` \
      annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to \
      flatten a document with hard newlines.")
  | taintedFormatting
    (stx : Syntax)
    (msg : String := "Formatting of the document produced by the current set of `[fmt]` \
      annotations contains a part that always exceeds the maximum column width within which \
      the formatter attempts to find optimal configurations (200). This issue is commonly caused \
      by syntax in the document that is not formatted (e.g. because there is no `[fmt]` attribute \
      for it) and is also very long in the input document. To format the parts of the document \
      that are formatteable, either break up the document that is not formatted or write a \
      formatter for it.")
  | malformedInputSyntax
    (stx : Syntax)
    (malformedPortion? : Option Substring.Raw)
    (reason : String)
    (msg : String :=
      let msg := s!"Input syntax to the formatter is malformed: {reason}."
      match malformedPortion? with
      | none => msg
      | some malformedPortion => s!"{msg} Offending portion of the input syntax: \
        {malformedPortion.toString}")
  | ambiguousChoiceNode
    (stx : Syntax)
    (msg : String := s!"A choice node was not disambiguated by the elaborator:\n{toString stx}")
  | headerError
    (stx : Syntax)
    (msg : String := s!"Cannot format file with header errors.")
  | parseError
    (msg : String := s!"Cannot format file with parse errors.")
  | earlyTerminationCommand
    (msg : String := s!"Cannot format file with early termination commands (e.g. `#exit`).")
  | raw
    (msg : String)
  deriving Inhabited

public instance : ToString Error where
  toString
    | .emptyInputSyntax (msg := msg) ..
    | .partialFormatter (msg := msg) ..
    | .formattingFailure (msg := msg) ..
    | .taintedFormatting (msg := msg) ..
    | .malformedInputSyntax (msg := msg) ..
    | .ambiguousChoiceNode (msg := msg) ..
    | .headerError (msg := msg) ..
    | .parseError (msg := msg) ..
    | .earlyTerminationCommand (msg := msg) ..
    | .raw (msg := msg) .. => msg

public def Error.ofFormattingError (stx : Syntax) : FormattingError → Error
  | .failure => .formattingFailure stx
  | .tainted => .taintedFormatting stx
