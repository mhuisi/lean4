/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Term
import Init.Data
import Init.While

namespace Lean.Fmt

public def fmtProjLike (lhs : TaggedDoc) (dotTk : Syntax) (field : Syntax) : FmtM TaggedDoc := do
  let dotTk ← fmt dotTk
  let field ← fmt field
  return propagateStickyness lhs fun lhs =>
    mkSelfDelimited <| Layouts.atomic #[lhs, dotTk, field]

public def allowAppArgFill : Syntax → Bool
  | `(Parser.Term.fun| $_:fun) => false
  | `(Parser.Term.paren| ($_:fun)) => false
  | `(Parser.Term.namedArgument| ($_:ident := $_:fun)) => false
  | _ => true

public def fmtFixedApp' (f : TaggedDoc) (args : Array Syntax)
    (format : Layouts.Types.ApplicationFormat := { parenthesize := true, respectPseudoAlignment := true })
    : FmtM (TaggedDoc × Array TaggedDoc) := do
  let mut args : Array (Fillable TaggedDoc) ← args.mapM fun arg => do
    return ({ v := ← fmt arg, allowFill := allowAppArgFill arg })
  if args[0...args.size - 1].all (·.allowFill) then
    args := args.modify (args.size - 1) fun lastArg => { lastArg with allowFill := true }
  let app := Layouts.applicationWithSomeFilled (format := format) <| #[⟨f, true⟩] ++ args
  return (app, args.map (·.v))

public def fmtFixedApp (f : TaggedDoc) (args : Array Syntax)
    (format : Layouts.Types.ApplicationFormat := { parenthesize := true, respectPseudoAlignment := true })
    : FmtM TaggedDoc := do
  let (app, _) ← fmtFixedApp' f args format
  return app

public def fmtAppLike (terms : Array Syntax) : FmtM TaggedDoc := do
  if terms.isEmpty then
    return empty
  let fStx := terms[0]!
  let args := terms[1...*].toArray
  let mut (f, format) ← do
    match fStx with
    | `($lhs:term.%$dotTk$field) =>
      let lhs ← fmt lhs
      let format : Layouts.Types.ApplicationFormat := { sparse := lhs.isBracketed, parenthesize := true, respectPseudoAlignment := true }
      pure (← fmtProjLike lhs dotTk field, format)
    | _ =>
      pure (← fmt fStx, { parenthesize := true, respectPseudoAlignment := true })
  let (app, args') ← fmtFixedApp' f args format
  if args'.size = 1 then
    let arg := args'[0]!
    if let some stickyArg := getSticky? arg then
      if propagatesRhsStickiness (← read).env ⟨fStx⟩ then
        return sticky app app stickyArg.kind
  return app
