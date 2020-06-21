/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Elab.Command

namespace Lean
namespace Elab
namespace Command

structure Attribute :=
(name : Name) (args : Syntax := Syntax.missing)

instance Attribute.hasFormat : HasFormat Attribute :=
⟨fun attr => Format.bracket "@[" (toString attr.name ++ (if attr.args.isMissing then "" else toString attr.args)) "]"⟩

inductive Visibility
| regular | «protected» | «private»

instance Visibility.hasToString : HasToString Visibility :=
⟨fun v => match v with
 | Visibility.regular   => "regular"
 | Visibility.private   => "private"
 | Visibility.protected => "protected"⟩

structure Modifiers :=
(docString       : Option String := none)
(visibility      : Visibility := Visibility.regular)
(isNoncomputable : Bool := false)
(isPartial       : Bool := false)
(isUnsafe        : Bool := false)
(attrs           : Array Attribute := #[])

def Modifiers.addAttribute (modifiers : Modifiers) (attr : Attribute) : Modifiers :=
{ modifiers with attrs := modifiers.attrs.push attr }

instance Modifiers.hasFormat : HasFormat Modifiers :=
⟨fun m =>
  let components : List Format :=
    (match m.docString with
     | some str => ["/--" ++ str ++ "-/"]
     | none     => [])
    ++ (match m.visibility with
     | Visibility.regular   => []
     | Visibility.protected => ["protected"]
     | Visibility.private   => ["private"])
    ++ (if m.isNoncomputable then ["noncomputable"] else [])
    ++ (if m.isPartial then ["partial"] else [])
    ++ (if m.isUnsafe then ["unsafe"] else [])
    ++ m.attrs.toList.map (fun attr => fmt attr);
  Format.bracket "{" (Format.joinSep components ("," ++ Format.line)) "}"⟩

instance Modifiers.hasToString : HasToString Modifiers := ⟨toString ∘ format⟩

def elabAttr (stx : Syntax) : CommandElabM Attribute := do
-- rawIdent >> many attrArg
let nameStx := stx.getArg 0;
attrName ← match nameStx.isIdOrAtom? with
  | none     => throwError nameStx "identifier expected"
  | some str => pure $ mkNameSimple str;
env ← getEnv;
unless (isAttribute env attrName) $
  throwError stx ("unknown attribute [" ++ attrName ++ "]");
let args := stx.getArg 1;
-- the old frontend passes Syntax.missing for empty args, for reasons
let args := if args.getNumArgs == 0 then Syntax.missing else args;
pure { name := attrName, args := args }

def elabAttrs (stx : Syntax) : CommandElabM (Array Attribute) :=
(stx.getArg 1).foldSepArgsM
  (fun stx attrs => do
    attr ← elabAttr stx;
    pure $ attrs.push attr)
  #[]

def elabModifiers (stx : Syntax) : CommandElabM Modifiers := do
let docCommentStx := stx.getArg 0;
let attrsStx      := stx.getArg 1;
let visibilityStx := stx.getArg 2;
let noncompStx    := stx.getArg 3;
let unsafeStx     := stx.getArg 4;
let partialStx    := stx.getArg 5;
docString ← match docCommentStx.getOptional? with
  | none   => pure none
  | some s => match s.getArg 1 with
    | Syntax.atom _ val => pure (some (val.extract 0 (val.bsize - 2)))
    | _                 => throwError s ("unexpected doc string " ++ toString (s.getArg 1));
visibility ← match visibilityStx.getOptional? with
  | none   => pure Visibility.regular
  | some v =>
    let kind := v.getKind;
    if kind == `Lean.Parser.Command.private then pure Visibility.private
    else if kind == `Lean.Parser.Command.protected then pure Visibility.protected
    else throwError v "unexpected visibility modifier";
attrs ← match attrsStx.getOptional? with
  | none       => pure #[]
  | some attrs => elabAttrs attrs;
pure {
  docString       := docString,
  visibility      := visibility,
  isPartial       := !partialStx.isNone,
  isUnsafe        := !unsafeStx.isNone,
  isNoncomputable := !noncompStx.isNone,
  attrs           := attrs
}

def mkDeclName (modifiers : Modifiers) (atomicName : Name) : CommandElabM Name := do
currNamespace ← getCurrNamespace;
let declName := currNamespace ++ atomicName;
match modifiers.visibility with
| Visibility.private => do
  env ← getEnv;
  pure $ mkPrivateName env declName
| _                  => pure declName

def checkNotAlreadyDeclared (ref : Syntax) (declName : Name) : CommandElabM Unit := do
env ← getEnv;
when (env.contains declName) $
  match privateToUserName? declName with
  | none          => throwError ref ("'" ++ declName ++ "' has already been declared")
  | some declName => throwError ref ("private declaration '" ++ declName ++ "' has already been declared");
when (env.contains (mkPrivateName env declName)) $
  throwError ref ("a private declaration '" ++ declName ++ "' has already been declared");
match privateToUserName? declName with
| none => pure ()
| some declName =>
  when (env.contains declName) $
    throwError ref ("a non-private declaration '" ++ declName ++ "' has already been declared")

def applyAttributes (ref : Syntax) (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : CommandElabM Unit :=
attrs.forM $ fun attr => do
 env ← getEnv;
 match getAttributeImpl env attr.name with
 | Except.error errMsg => throwError ref errMsg
 | Except.ok attrImpl  =>
   when (attrImpl.applicationTime == applicationTime) $ do
     env ← getEnv;
     env ← liftIO ref $ attrImpl.add env declName attr.args true;
     setEnv env

end Command
end Elab
end Lean
