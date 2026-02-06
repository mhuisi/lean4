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
public import Lean.Util.ShareCommon

namespace Lean

public structure Fmt.Context where
  env : Environment

public structure Fmt.State where
  shareCommonState : ShareCommon.State ShareCommon.objectFactory
  freshTagId : TagId
  tags : Std.HashMap TagId Syntax.Range

public structure Fmt.TaggedDoc where
  doc : Fmt.Doc

public abbrev FmtM α := ReaderT Fmt.Context (ExceptT Unit (StateT Fmt.State Id)) α
public abbrev Fmt := Syntax → FmtM Fmt.TaggedDoc

public def FmtM.run (env : Environment) (act : FmtM α) : Option α :=
  ReaderT.run act { env }
    |>.run' { shareCommonState := default, freshTagId := Nat.zero, tags := ∅ }
    |>.toOption

instance : MonadShareCommon FmtM where
  withShareCommon v _ := modifyGet fun s =>
    let (v, shareCommonState) := s.shareCommonState.shareCommon v
    (v, { s with shareCommonState })

namespace Fmt

public def untagged (doc : Fmt.Doc) : TaggedDoc :=
  ⟨doc⟩

public def tagged (doc : Fmt.Doc) (ref : Syntax) : FmtM TaggedDoc := do
  let some range := ref.getRange?
    | return ⟨doc⟩
  modify fun s =>
    let currentTagId : Nat := s.freshTagId
    { s with
      freshTagId := currentTagId + 1
      tags := s.tags.insertIfNew currentTagId range
    }
  return ⟨doc⟩

public def TaggedDoc.tag (d : TaggedDoc) (ref : Syntax) : FmtM TaggedDoc :=
  tagged d.doc ref

public def failure : TaggedDoc :=
  untagged .failure
public def newline (flattened? : Option String) : TaggedDoc :=
  untagged (.newline flattened?)
public def nl : TaggedDoc :=
  untagged .nl
public def «break» : TaggedDoc :=
  untagged .break
public def hardNl : TaggedDoc :=
  untagged .hardNl
public def text (s : String) (ref : Syntax) : FmtM TaggedDoc :=
  tagged (.text s) ref
public def space : TaggedDoc :=
  untagged (.text " ")
public def nested (d : TaggedDoc) : TaggedDoc :=
  untagged <| .nested d.doc
public def hardNested (d : TaggedDoc) : TaggedDoc :=
  untagged <| .hardNested d.doc
public def flattened (d : TaggedDoc) : TaggedDoc :=
  untagged <| .flattened d.doc
public def maybeFlattened (d : TaggedDoc) : TaggedDoc :=
  untagged <| .maybeFlattened d.doc
public def unindented (d : TaggedDoc) : TaggedDoc :=
  untagged <| .unindented d.doc
public def full (d : TaggedDoc) : TaggedDoc :=
  untagged <| .full d.doc
public def either (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .either a.doc b.doc
public def append (a b : TaggedDoc) : TaggedDoc :=
  untagged <| .append a.doc b.doc
public def join (ds : Array TaggedDoc) : TaggedDoc :=
  untagged <| .join <| ds.map (·.doc)

public instance : Append TaggedDoc where
  append := append

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

public def fmt : Fmt := fun stx => match stx with
  | .missing => pure <| failure
  | .atom _ val => text val stx
  | .ident _ _ val _ => text val.toString stx
  | .node .. => do
    let ctx ← read
    let fmts := fmtAttribute.getValues ctx.env stx.getKind
    let some f := fmts.head?
      | panic! s!"No formatter found for kind '{stx.getKind}' of the following syntax: {stx}"
    let r ← f stx
    let r ← r.tag stx
    withShareCommon r
