/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.ToString
public import Lean.Data.Fmt.Basic

public inductive Lean.Fmt.Error where
  | partialFormatter
    (kind : SyntaxNodeKind)
    (msg : String := s!"Formatter for syntax kind `{kind}` is partial and does not handle the full \
      syntax of `{kind}`.")
  | formattingFailure
    (stx : Syntax)
    (doc : Doc)
    (msg : String := "Formatting of the document produced by the current set of `[fmt]` \
      annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to \
      flatten a document with hard newlines.")
  | malformedInputSyntax
    (stx : Syntax)
    (malformedPortion : Substring.Raw)
    (reason : String)
    (msg : String := s!"Input syntax to the formatter is malformed: {reason}. Offending portion \
      of the input syntax: {malformedPortion.toString}")
  | raw
    (msg : String)
  deriving Inhabited
