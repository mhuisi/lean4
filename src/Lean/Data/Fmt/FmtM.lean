/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Formatter
public import Lean.KeyedDeclsAttribute
import Lean.Parser.Extension
import Lean.ExtraModUses
import Lean.Elab.InfoTree.Main

namespace Lean

public structure Fmt.Context where
  env : Environment

public abbrev Fmt := Syntax → ReaderT Fmt.Context (ExceptT Unit Id) Fmt.Doc

namespace Fmt

unsafe builtin_initialize fmtAttribute : KeyedDeclsAttribute Fmt ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_fmt,
    name := `fmt,
    descr := "Register an Fmt formatter for a syntax node kind.",
    valueTypeName := `Lean.Fmt,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      if ! (builtin && (env.find? id).isSome || Parser.isValidSyntaxNodeKind env id) then
        throwError "Invalid `[fmt]` argument: Unknown syntax kind `{id}`"
      if (← getEnv).contains id then
        recordExtraModUseFromDecl (isMeta := false) id
        if (← Elab.getInfoState).enabled then
          Elab.addConstInfo stx id none
      pure id
  }

public def fmt : Fmt := fun stx => do
  let ctx ← read
  let fmts := fmtAttribute.getValues ctx.env stx.getKind
  let some f := fmts.head?
    | panic! s!"No formatter found for kind '{stx.getKind}' of the following syntax: {stx}"
  f stx
