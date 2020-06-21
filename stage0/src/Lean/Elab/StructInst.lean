/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.FindExpr
import Lean.Elab.App
import Lean.Elab.Binders
import Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term
namespace StructInst

/- parser! "{" >> optional (try (termParser >> "with")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> "}" -/

/-
If `stx` is of the form `{ s with ... }` and `s` is not a local variable, expand into `let src := s; { src with ... }`.
-/
private def expandNonAtomicExplicitSource (stx : Syntax) : TermElabM (Option Syntax) :=
withFreshMacroScope $
  let sourceOpt := stx.getArg 1;
  if sourceOpt.isNone then pure none  else do
    let source := sourceOpt.getArg 0;
    fvar? ← isLocalTermId? source;
    match fvar? with
    | some _ => pure none
    | none   => do
      src ← `(src);
      let sourceOpt := sourceOpt.setArg 0 src;
      let stxNew    := stx.setArg 1 sourceOpt;
      `(let src := $source; $stxNew)

inductive Source
| none     -- structure instance source has not been provieded
| implicit (stx : Syntax) -- `..`
| explicit (stx : Syntax) (src : Expr) -- `src with`

instance Source.inhabited : Inhabited Source := ⟨Source.none⟩

def Source.isNone : Source → Bool
| Source.none => true
| _           => false

def setStructSourceSyntax (structStx : Syntax) : Source → Syntax
| Source.none           => (structStx.setArg 1 mkNullNode).setArg 3 mkNullNode
| Source.implicit stx   => (structStx.setArg 1 mkNullNode).setArg 3 stx
| Source.explicit stx _ => (structStx.setArg 1 stx).setArg 3 mkNullNode

private def getStructSource (stx : Syntax) : TermElabM Source :=
let explicitSource := stx.getArg 1;
let implicitSource := stx.getArg 3;
if explicitSource.isNone && implicitSource.isNone then
  pure Source.none
else if explicitSource.isNone then
  pure $ Source.implicit implicitSource
else if implicitSource.isNone then do
  fvar? ← isLocalTermId? (explicitSource.getArg 0);
  match fvar? with
  | none      => unreachable! -- expandNonAtomicExplicitSource must have been used when we get here
  | some src  => pure $ Source.explicit explicitSource src
else
  throwError stx "invalid structure instance `with` and `..` cannot be used together"

/-
  We say a `{ ... }` notation is a `modifyOp` if it contains only one
  ```
  def structInstArrayRef := parser! "[" >> termParser >>"]"
  ``` -/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
let args := (stx.getArg 2).getArgs;
s? ← args.foldSepByM
  (fun arg s? =>
    /- Remark: the syntax for `structInstField` is
       ```
       def structInstLVal   := (ident <|> numLit <|> structInstArrayRef) >> many (group ("." >> (ident <|> numLit)) <|> structInstArrayRef)
       def structInstField  := parser! structInstLVal >> " := " >> termParser
       ``` -/
    let lval := arg.getArg 0;
    let k    := lval.getKind;
    if k == `Lean.Parser.Term.structInstArrayRef then
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwError arg "invalid {...} notation, at most one `[..]` at a given level"
        else
          throwError arg "invalid {...} notation, can't mix field and `[..]` at a given level"
    else
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwError arg "invalid {...} notation, can't mix field and `[..]` at a given level"
        else
          pure s?)
  none;
match s? with
| none   => pure none
| some s => if (s.getArg 0).getKind == `Lean.Parser.Term.structInstArrayRef then pure s? else pure none

private def elabModifyOp (stx modifyOp source : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
let continue (val : Syntax) : TermElabM Expr := do {
  let lval := modifyOp.getArg 0;
  let idx  := lval.getArg 1;
  let self := source.getArg 0;
  stxNew ← `($(self).modifyOp (idx := $idx) (fun s => $val));
  trace `Elab.struct.modifyOp stx $ fun _ => stx ++ "\n===>\n" ++ stxNew;
  withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
}; do
trace `Elab.struct.modifyOp stx $ fun _ => modifyOp ++ "\nSource: " ++ source;
let rest := modifyOp.getArg 1;
if rest.isNone then do
  continue (modifyOp.getArg 3)
else do
  s ← `(s);
  let valFirst  := rest.getArg 0;
  let valFirst  := if valFirst.getKind == `Lean.Parser.Term.structInstArrayRef then valFirst else valFirst.getArg 1;
  let restArgs  := rest.getArgs;
  let valRest   := mkNullNode (restArgs.extract 1 restArgs.size);
  let valField  := modifyOp.setArg 0 valFirst;
  let valField  := valField.setArg 1 valRest;
  let valSource := source.modifyArg 0 $ fun _ => s;
  let val       := stx.setArg 1 valSource;
  let val       := val.setArg 2 $ mkNullNode #[valField];
  trace `Elab.struct.modifyOp stx $ fun _ => stx ++ "\nval: " ++ val;
  continue val

/- Get structure name and elaborate explicit source (if available) -/
private def getStructName (stx : Syntax) (expectedType? : Option Expr) (sourceView : Source) : TermElabM Name := do
let ref := stx;
tryPostponeIfNoneOrMVar expectedType?;
let useSource : Unit → TermElabM Name := fun _ =>
  match sourceView with
  | Source.explicit _ src => do
    srcType ← inferType stx src;
    srcType ← whnf stx srcType;
    tryPostponeIfMVar srcType;
    match srcType.getAppFn with
    | Expr.const constName _ _ => pure constName
    | _ => throwError stx ("invalid {...} notation, source type is not of the form (C ...)" ++ indentExpr srcType)
  | _ => throwError ref ("invalid {...} notation, expected type is not of the form (C ...)" ++ indentExpr expectedType?.get!);
match expectedType? with
| none => useSource ()
| some expectedType => do
  expectedType ← whnf ref expectedType;
  match expectedType.getAppFn with
  | Expr.const constName _ _ => pure constName
  | _                        => useSource ()

inductive FieldLHS
| fieldName  (ref : Syntax) (name : Name)
| fieldIndex (ref : Syntax) (idx : Nat)
| modifyOp   (ref : Syntax) (index : Syntax)

instance FieldLHS.inhabited : Inhabited FieldLHS := ⟨FieldLHS.fieldName (arbitrary _) (arbitrary _)⟩
instance FieldLHS.hasFormat : HasFormat FieldLHS :=
⟨fun lhs => match lhs with
  | FieldLHS.fieldName _ n  => fmt n
  | FieldLHS.fieldIndex _ i => fmt i
  | FieldLHS.modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

inductive FieldVal (σ : Type)
| term  (stx : Syntax) : FieldVal
| nested (s : σ)       : FieldVal
| default              : FieldVal -- mark that field must be synthesized using default value

structure Field (σ : Type) :=
(ref : Syntax) (lhs : List FieldLHS) (val : FieldVal σ) (expr? : Option Expr := none)

instance Field.inhabited {σ} : Inhabited (Field σ) := ⟨⟨arbitrary _, [], FieldVal.term (arbitrary _), arbitrary _⟩⟩

def Field.isSimple {σ} : Field σ → Bool
| { lhs := [_], .. } => true
| _                  => false

inductive Struct
| mk (ref : Syntax) (structName : Name) (fields : List (Field Struct)) (source : Source)

instance Struct.inhabited : Inhabited Struct := ⟨⟨arbitrary _, arbitrary _, [], arbitrary _⟩⟩

abbrev Fields := List (Field Struct)

def Struct.ref : Struct → Syntax
| ⟨ref, _, _, _⟩ => ref

def Struct.structName : Struct → Name
| ⟨_, structName, _, _⟩ => structName

def Struct.fields : Struct → Fields
| ⟨_, _, fields, _⟩ => fields

def Struct.source : Struct → Source
| ⟨_, _, _, s⟩ => s

def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
Format.joinSep field.lhs " . " ++ " := " ++
  match field.val with
  | FieldVal.term v   => v.prettyPrint
  | FieldVal.nested s => formatStruct s
  | FieldVal.default  => "<default>"

partial def formatStruct : Struct → Format
| ⟨_, structName, fields, source⟩ =>
  let fieldsFmt := Format.joinSep (fields.map (formatField formatStruct)) ", ";
  match source with
  | Source.none           => "{" ++ fieldsFmt ++ "}"
  | Source.implicit _     => "{" ++ fieldsFmt ++ " .. }"
  | Source.explicit _ src => "{" ++ format src ++ " with " ++ fieldsFmt ++ "}"

instance Struct.hasFormat : HasFormat Struct     := ⟨formatStruct⟩
instance Struct.hasToString : HasToString Struct := ⟨toString ∘ format⟩

instance Field.hasFormat   : HasFormat (Field Struct) := ⟨formatField formatStruct⟩
instance Field.hasToString : HasToString (Field Struct) := ⟨toString ∘ format⟩

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := parser! structInstLVal >> " := " >> termParser
   def structInstLVal   := (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
   def structInstArrayRef := parser! "[" >> termParser >>"]"
-/

-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
| FieldLHS.modifyOp   stx _    => stx
| FieldLHS.fieldName  stx name => if first then mkIdentFrom stx name else mkNullNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
| FieldLHS.fieldIndex stx _    => if first then stx else mkNullNode #[mkAtomFrom stx ".", stx]

def FieldVal.toSyntax : FieldVal Struct → Syntax
| FieldVal.term stx => stx
| _                 => unreachable!

def Field.toSyntax : Field Struct → Syntax
| field =>
  let stx := field.ref;
  let stx := stx.setArg 3 field.val.toSyntax;
  match field.lhs with
  | first::rest =>
    let stx := stx.setArg 0 $ first.toSyntax true;
    let stx := stx.setArg 1 $ mkNullNode $ rest.toArray.map (FieldLHS.toSyntax false);
    stx
  | _ => unreachable!

private def toFieldLHS (stx : Syntax) : Except String FieldLHS :=
if stx.getKind == `Lean.Parser.Term.structInstArrayRef then
  pure $ FieldLHS.modifyOp stx (stx.getArg 1)
else
  -- Note that the representation of the first field is different.
  let stx := if stx.getKind == nullKind then stx.getArg 1 else stx;
  if stx.isIdent then pure $ FieldLHS.fieldName stx stx.getId
  else match stx.isFieldIdx? with
    | some idx => pure $ FieldLHS.fieldIndex stx idx
    | none     => throw "unexpected structure syntax"

private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : Except String Struct := do
let args      := (stx.getArg 2).getArgs;
let fieldsStx := args.filter $ fun arg => arg.getKind == `Lean.Parser.Term.structInstField;
fields ← fieldsStx.toList.mapM $ fun fieldStx => do {
  let val   := fieldStx.getArg 3;
  first ← toFieldLHS (fieldStx.getArg 0);
  rest  ← (fieldStx.getArg 1).getArgs.toList.mapM toFieldLHS;
  pure $ ({ref := fieldStx, lhs := first :: rest, val := FieldVal.term val } : Field Struct)
};
pure ⟨stx, structName, fields, source⟩

def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
match s with
| ⟨ref, structName, fields, source⟩ => do fields ← f fields; pure ⟨ref, structName, fields, source⟩

@[inline] def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
Id.run $ s.modifyFieldsM f

def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
s.modifyFields $ fun _ => fields

private def expandCompositeFields (s : Struct) : Struct :=
s.modifyFields $ fun fields => fields.map $ fun field => match field with
  | { lhs := FieldLHS.fieldName ref (Name.str Name.anonymous _ _) :: rest, .. } => field
  | { lhs := FieldLHS.fieldName ref n@(Name.str _ _ _) :: rest, .. } =>
    let newEntries := n.components.map $ FieldLHS.fieldName ref;
    { field with lhs := newEntries ++ rest }
  | _ => field

private def expandNumLitFields (s : Struct) : TermElabM Struct :=
s.modifyFieldsM $ fun fields => do
  env ← getEnv;
  let fieldNames := getStructureFields env s.structName;
  fields.mapM $ fun field => match field with
    | { lhs := FieldLHS.fieldIndex ref idx :: rest, .. } =>
      if idx == 0 then throwError ref "invalid field index, index must be greater than 0"
      else if idx > fieldNames.size then throwError ref ("invalid field index, structure has only #" ++ toString fieldNames.size ++ " fields")
      else pure { field with lhs := FieldLHS.fieldName ref (fieldNames.get! $ idx - 1) :: rest }
    | _ => pure field

/- For example, consider the following structures:
   ```
   structure A := (x : Nat)
   structure B extends A := (y : Nat)
   structure C extends B := (z : Bool)
   ```
   This method expands parent structure fields using the path to the parent structure.
   For example,
   ```
   { x := 0, y := 0, z := true : C }
   ```
   is expanded into
   ```
   { toB.toA.x := 0, toB.y := 0, z := true : C }
   ``` -/
private def expandParentFields (s : Struct) : TermElabM Struct := do
env ← getEnv;
s.modifyFieldsM $ fun fields => fields.mapM $ fun field => match field with
  | { lhs := FieldLHS.fieldName ref fieldName :: rest, .. } =>
    match findField? env s.structName fieldName with
    | none => throwError ref ("'" ++ fieldName ++ "' is not a field of structure '" ++ s.structName ++ "'")
    | some baseStructName =>
      if baseStructName == s.structName then pure field
      else match getPathToBaseStructure? env baseStructName s.structName with
        | some path => do
          let path := path.map $ fun funName => match funName with
            | Name.str _ s _ => FieldLHS.fieldName ref (mkNameSimple s)
            | _              => unreachable!;
          pure { field with lhs := path ++ field.lhs }
        | _ => throwError ref ("failed to access field '" ++ fieldName ++ "' in parent structure")
  | _ => pure field

private abbrev FieldMap := HashMap Name Fields

private def mkFieldMap (fields : Fields) : TermElabM FieldMap :=
fields.foldlM
  (fun fieldMap field =>
    match field.lhs with
    | FieldLHS.fieldName _ fieldName :: rest =>
      match fieldMap.find? fieldName with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwError field.ref ("field '" ++ fieldName ++ "' has already beed specified")
        else
          pure $ fieldMap.insert fieldName (field::prevField::restFields)
      | _ => pure $ fieldMap.insert fieldName [field]
    | _ => unreachable!)
  {}

private def isSimpleField? : Fields → Option (Field Struct)
| [field] => if field.isSimple then some field else none
| _       => none

private def getFieldIdx (ref : Syntax) (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
match fieldNames.findIdx? $ fun n => n == fieldName with
| some idx => pure idx
| none     => throwError ref ("field '" ++ fieldName ++ "' is not a valid field of '" ++ structName ++ "'")

private def mkProjStx (s : Syntax) (fieldName : Name) : Syntax :=
Syntax.node `Lean.Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

private def mkSubstructSource (ref : Syntax) (structName : Name) (fieldNames : Array Name) (fieldName : Name) (src : Source) : TermElabM Source :=
match src with
| Source.explicit stx src => do
  idx ← getFieldIdx ref structName fieldNames fieldName;
  let stx := stx.modifyArg 0 $ fun stx => mkProjStx stx fieldName;
  pure $ Source.explicit stx (mkProj structName idx src)
| s => pure s

@[specialize] private def groupFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
env ← getEnv;
let fieldNames := getStructureFields env s.structName;
s.modifyFieldsM $ fun fields => do
  fieldMap ← mkFieldMap fields;
  fieldMap.toList.mapM $ fun ⟨fieldName, fields⟩ =>
    match isSimpleField? fields with
    | some field => pure field
    | none => do
      let substructFields := fields.map $ fun field => { field with lhs := field.lhs.tail! };
      substructSource ← mkSubstructSource s.ref s.structName fieldNames fieldName s.source;
      let field := fields.head!;
      match Lean.isSubobjectField? env s.structName fieldName with
      | some substructName => do
        let substruct := Struct.mk s.ref substructName substructFields substructSource;
        substruct ← expandStruct substruct;
        pure { field with lhs := [field.lhs.head!], val := FieldVal.nested substruct }
      | none => do
        -- It is not a substructure field. Thus, we wrap fields using `Syntax`, and use `elabTerm` to process them.
        let valStx := s.ref; -- construct substructure syntax using s.ref as template
        let valStx := valStx.setArg 4 mkNullNode; -- erase optional expected type
        let args   := substructFields.toArray.map $ Field.toSyntax;
        let valStx := valStx.setArg 2 (mkSepStx args (mkAtomFrom s.ref ","));
        let valStx := setStructSourceSyntax valStx substructSource;
        pure { field with lhs := [field.lhs.head!], val := FieldVal.term valStx }

def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
fields.find? $ fun field =>
  match field.lhs with
  | [FieldLHS.fieldName _ n] => n == fieldName
  | _                        => false

@[specialize] private def addMissingFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
env ← getEnv;
let fieldNames := getStructureFields env s.structName;
let ref := s.ref;
fields ← fieldNames.foldlM
  (fun fields fieldName => do
    match findField? s.fields fieldName with
    | some field => pure $ field::fields
    | none       =>
      let addField (val : FieldVal Struct) : TermElabM Fields := do {
        pure $ { ref := s.ref, lhs := [FieldLHS.fieldName s.ref fieldName], val := val } :: fields
      };
      match Lean.isSubobjectField? env s.structName fieldName with
      | some substructName => do
        substructSource ← mkSubstructSource s.ref s.structName fieldNames fieldName s.source;
        let substruct := Struct.mk s.ref substructName [] substructSource;
        substruct ← expandStruct substruct;
        addField (FieldVal.nested substruct)
      | none =>
        match s.source with
        | Source.none           => addField FieldVal.default
        | Source.implicit _     => addField (FieldVal.term (mkHole s.ref))
        | Source.explicit stx _ =>
          -- stx is of the form `optional (try (termParser >> "with"))`
          let src := (stx.getArg 0).getArg 0;
          let val := mkProjStx src fieldName;
          addField (FieldVal.term val))
  [];
pure $ s.setFields fields.reverse

private partial def expandStruct : Struct → TermElabM Struct
| s => do
  let s := expandCompositeFields s;
  s ← expandNumLitFields s;
  s ← expandParentFields s;
  s ← groupFields expandStruct s;
  addMissingFields expandStruct s

structure CtorHeaderResult :=
(ctorFn     : Expr)
(ctorFnType : Expr)
(instMVars  : Array MVarId := #[])

private def mkCtorHeaderAux (ref : Syntax) : Nat → Expr → Expr → Array MVarId → TermElabM CtorHeaderResult
| 0,   type, ctorFn, instMVars => pure { ctorFn := ctorFn, ctorFnType := type, instMVars := instMVars }
| n+1, type, ctorFn, instMVars => do
  type ← whnfForall ref type;
  match type with
  | Expr.forallE _ d b c =>
    match c.binderInfo with
    | BinderInfo.instImplicit => do
      a ← mkFreshExprMVar ref d MetavarKind.synthetic;
      mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) (instMVars.push a.mvarId!)
    | _ => do
      a ← mkFreshExprMVar ref d;
      mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) instMVars
  | _ => throwError ref "unexpected constructor type"

private partial def getForallBody : Nat → Expr → Option Expr
| i+1, Expr.forallE _ _ b _ => getForallBody i b
| i+1, _                    => none
| 0,   type                 => type

private def propagateExpectedType (ref : Syntax) (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit :=
match expectedType? with
| none              => pure ()
| some expectedType =>
  match getForallBody numFields type with
    | none           => pure ()
    | some typeBody =>
      unless typeBody.hasLooseBVars $ do
        _ ← isDefEq ref expectedType typeBody;
        pure ()

private def mkCtorHeader (ref : Syntax) (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
lvls ← ctorVal.lparams.mapM $ fun _ => mkFreshLevelMVar ref;
let val  := Lean.mkConst ctorVal.name lvls;
let type := (ConstantInfo.ctorInfo ctorVal).instantiateTypeLevelParams lvls;
r ← mkCtorHeaderAux ref ctorVal.nparams type val #[];
propagateExpectedType ref r.ctorFnType ctorVal.nfields expectedType?;
synthesizeAppInstMVars ref r.instMVars;
pure r

def markDefaultMissing (e : Expr) : Expr :=
mkAnnotation `structInstDefault e

def isDefaultMissing? (e : Expr) : Option Expr :=
isAnnotation? `structInstDefault e

def throwFailedToElabField {α} (ref : Syntax) (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
throwError ref ("failed to elaborate field '" ++ fieldName ++ "' of '" ++ structName ++ ", " ++ msgData)

private partial def elabStruct : Struct → Option Expr → TermElabM (Expr × Struct)
| s, expectedType? => do
  env ← getEnv;
  let ctorVal := getStructureCtor env s.structName;
  { ctorFn := ctorFn, ctorFnType := ctorFnType, .. } ← mkCtorHeader s.ref ctorVal expectedType?;
  (e, _, fields) ← s.fields.foldlM
    (fun (acc : Expr × Expr × Fields) field =>
      let (e, type, fields) := acc;
      match field.lhs with
      | [FieldLHS.fieldName ref fieldName] => do
        type ← whnfForall field.ref type;
        match type with
        | Expr.forallE _ d b c =>
          let continue (val : Expr) (field : Field Struct) : TermElabM (Expr × Expr × Fields) := do {
            let e     := mkApp e val;
            let type  := b.instantiate1 val;
            let field := { field with expr? := some val };
            pure (e, type, field::fields)
          };
          match field.val with
          | FieldVal.term stx => do val ← elabTerm stx (some d); val ← ensureHasType stx d val; continue val field
          | FieldVal.nested s => do (val, sNew) ← elabStruct s (some d); val ← ensureHasType s.ref d val; continue val { field with val := FieldVal.nested sNew }
          | FieldVal.default  => do val ← mkFreshExprMVar field.ref (some d); continue (markDefaultMissing val) field
        | _ => throwFailedToElabField field.ref fieldName s.structName ("unexpected constructor type" ++ indentExpr type)
      | _ => throwError field.ref "unexpected unexpanded structure field")
    (ctorFn, ctorFnType, []);
  pure (e, s.setFields fields.reverse)

namespace DefaultFields

structure Context :=
-- We must search for default values overriden in derived structures
(structs : Array Struct := #[])
(allStructNames : Array Name := #[])
/-
Consider the following example:
```
structure A :=
(x : Nat := 1)

structure B extends A :=
(y : Nat := x + 1) (x := y + 1)

structure C extends B :=
(z : Nat := 2*y) (x := z + 3)
```
And we are trying to elaborate a structure instance for `C`. There are default values for `x` at `A`, `B`, and `C`.
We say the default value at `C` has distance 0, the one at `B` distance 1, and the one at `A` distance 2.
The field `maxDistance` specifies the maximum distance considered in a round of Default field computation.
Remark: since `C` does not set a default value of `y`, the default value at `B` is at distance 0.

The fixpoint for setting default values works in the following way.
- Keep computing default values using `maxDistance == 0`.
- We increase `maxDistance` whenever we failed to compute a new default value in a round.
- If `maxDistance > 0`, then we interrupt a round as soon as we compute some default value.
  We use depth-first search.
- We sign an error if no progress is made when `maxDistance` == structure hierarchy depth (2 in the example above).
-/
(maxDistance : Nat := 0)

structure State :=
(progress : Bool := false)

partial def collectStructNames : Struct → Array Name → Array Name
| struct, names =>
  let names := names.push struct.structName;
  struct.fields.foldl
    (fun names field =>
      match field.val with
      | FieldVal.nested struct => collectStructNames struct names
      | _ => names)
    names

partial def getHierarchyDepth : Struct → Nat
| struct =>
  struct.fields.foldl
    (fun max field =>
      match field.val with
      | FieldVal.nested struct => Nat.max max (getHierarchyDepth struct + 1)
      | _ => max)
    0

partial def findDefaultMissing? (mctx : MetavarContext) : Struct → Option (Field Struct)
| struct =>
  struct.fields.findSome? $ fun field =>
   match field.val with
   | FieldVal.nested struct => findDefaultMissing? struct
   | _ => match field.expr? with
     | none      => unreachable!
     | some expr => match isDefaultMissing? expr with
       | some (Expr.mvar mvarId _) => if mctx.isExprAssigned mvarId then none else some field
       | _                         => none

def getFieldName (field : Field Struct) : Name :=
match field.lhs with
| [FieldLHS.fieldName _ fieldName] => fieldName
| _ => unreachable!

abbrev M := ReaderT Context (StateT State TermElabM)

def isRoundDone : M Bool := do
ctx ← read;
s ← get;
pure (s.progress && ctx.maxDistance > 0)

def getFieldValue? (struct : Struct) (fieldName : Name) : Option Expr :=
struct.fields.findSome? $ fun field =>
  if getFieldName field == fieldName then
    field.expr?
  else
    none

partial def mkDefaultValueAux? (struct : Struct) : Expr → TermElabM (Option Expr)
| Expr.lam n d b c =>
  let ref := struct.ref;
  if c.binderInfo.isExplicit then
    let fieldName := n;
    match getFieldValue? struct fieldName with
    | none     => pure none
    | some val => do
      valType ← inferType ref val;
      condM (isDefEq ref valType d)
        (mkDefaultValueAux? (b.instantiate1 val))
        (pure none)
  else do
    arg ← mkFreshExprMVar ref d;
    mkDefaultValueAux? (b.instantiate1 arg)
| e =>
  if e.isAppOfArity `id 2 then
    pure (some e.appArg!)
  else
    pure (some e)

def mkDefaultValue? (struct : Struct) (cinfo : ConstantInfo) : TermElabM (Option Expr) := do
let ref := struct.ref;
us ← cinfo.lparams.mapM $ fun _ => mkFreshLevelMVar ref;
mkDefaultValueAux? struct (cinfo.instantiateValueLevelParams us)

/-- If `e` is a projection function of one of the given structures, then reduce it -/
def reduceProjOf? (structNames : Array Name) (e : Expr) : MetaM (Option Expr) := do
if !e.isApp then pure none
else match e.getAppFn with
  | Expr.const name _ _ => do
    env ← Meta.getEnv;
    if env.isProjectionFn name then
      match name with
      | Name.str structName fieldName _ => do
        if structNames.contains structName then
          Meta.unfoldDefinition? e
        else
          pure none
      | _ => pure none
    else
      pure none
  | _ => pure none

/-- Reduce default value. It performs beta reduction and projections of the given structures. -/
partial def reduce (structNames : Array Name) : Expr → MetaM Expr
| e@(Expr.lam _ _ _ _)     => Meta.lambdaTelescope e $ fun xs b => do b ← reduce b; Meta.mkLambda xs b
| e@(Expr.forallE _ _ _ _) => Meta.forallTelescope e $ fun xs b => do b ← reduce b; Meta.mkForall xs b
| e@(Expr.letE _ _ _ _ _)  => Meta.lambdaTelescope e $ fun xs b => do b ← reduce b; Meta.mkLambda xs b
| e@(Expr.proj _ i b _)    => do
  r? ← Meta.reduceProj? b i;
  match r? with
  | some r => reduce r
  | none   => do b ← reduce b; pure $ e.updateProj! b
| e@(Expr.app f _ _) => do
  r? ← reduceProjOf? structNames e;
  match r? with
  | some r => reduce r
  | none   => do
    let f := f.getAppFn;
    f' ← reduce f;
    if f'.isLambda then
      let revArgs := e.getAppRevArgs;
      reduce $ f'.betaRev revArgs
    else do
      args ← e.getAppArgs.mapM reduce;
      pure (mkAppN f' args)
| e@(Expr.mdata _ b _) => do
  b ← reduce b;
  if (isDefaultMissing? e).isSome && !b.isMVar then
    pure b
  else
    pure $ e.updateMData! b
| e@(Expr.mvar mvarId _) => do
  val? ← Meta.getExprMVarAssignment? mvarId;
  match val? with
  | some val => if val.isMVar then reduce val else pure val
  | none     => pure e
| e => pure e

partial def tryToSynthesizeDefaultAux (ref : Syntax) (structs : Array Struct) (allStructNames : Array Name) (maxDistance : Nat)
    (fieldName : Name) (mvarId : MVarId) : Nat → Nat → TermElabM Bool
| i, dist =>
  if dist > maxDistance then pure false
  else if h : i < structs.size then do
    let struct := structs.get ⟨i, h⟩;
    let defaultName := struct.structName ++ fieldName ++ `_default;
    env ← getEnv;
    match env.find? defaultName with
    | some cinfo@(ConstantInfo.defnInfo defVal) => do
      mctx ← getMCtx;
      val? ← mkDefaultValue? struct cinfo;
      match val? with
      | none     => do setMCtx mctx; tryToSynthesizeDefaultAux (i+1) (dist+1)
      | some val => do
        val ← liftMetaM struct.ref $ reduce allStructNames val;
        match val.find? $ fun e => (isDefaultMissing? e).isSome with
        | some _ => do setMCtx mctx; tryToSynthesizeDefaultAux (i+1) (dist+1)
        | none   => do
          mvarDecl ← getMVarDecl mvarId;
          val ← ensureHasType ref mvarDecl.type val;
          assignExprMVar mvarId val;
          pure true
    | _ => tryToSynthesizeDefaultAux (i+1) dist
  else
    pure false

def tryToSynthesizeDefault (ref : Syntax) (structs : Array Struct) (allStructNames : Array Name)
    (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
tryToSynthesizeDefaultAux ref structs allStructNames maxDistance fieldName mvarId 0 0

partial def step : Struct → M Unit
| struct => unlessM isRoundDone $ adaptReader (fun (ctx : Context) => { ctx with structs := ctx.structs.push struct }) $ do
  struct.fields.forM $ fun field =>
    match field.val with
    | FieldVal.nested struct => step struct
    | _ => match field.expr? with
      | none      => unreachable!
      | some expr => match isDefaultMissing? expr with
        | some (Expr.mvar mvarId _) =>
          unlessM (liftM $ isExprMVarAssigned mvarId) $ do
            ctx ← read;
            whenM (liftM $ tryToSynthesizeDefault field.ref ctx.structs ctx.allStructNames ctx.maxDistance (getFieldName field) mvarId) $ do
              modify $ fun s => { s with progress := true }
        | _ => pure ()

partial def propagateLoop (hierarchyDepth : Nat) : Nat → Struct → M Unit
| d, struct => do
  mctx ← liftM $ getMCtx;
  match findDefaultMissing? mctx struct with
  | none       => pure () -- Done
  | some field =>
    if d > hierarchyDepth then
      liftM $ throwError field.ref ("field '" ++ getFieldName field ++ "' is missing")
    else adaptReader (fun (ctx : Context) => { ctx with maxDistance := d }) $ do
      modify $ fun (s : State) => { s with progress := false };
      step struct;
      s ← get;
      if s.progress then do
        propagateLoop 0 struct
      else
        propagateLoop (d+1) struct

def propagate (struct : Struct) : TermElabM Unit :=
let hierarchyDepth := getHierarchyDepth struct;
let structNames := collectStructNames struct #[];
(propagateLoop hierarchyDepth 0 struct { allStructNames := structNames }).run' {}

end DefaultFields

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
structName ← getStructName stx expectedType? source;
env ← getEnv;
unless (isStructureLike env structName) $
  throwError stx ("invalid {...} notation, '" ++ structName ++ "' is not a structure");
match mkStructView stx structName source with
| Except.error ex  => throwError stx ex
| Except.ok struct => do
  struct ← expandStruct struct;
  trace `Elab.struct stx $ fun _ => toString struct;
  (r, struct) ← elabStruct struct expectedType?;
  DefaultFields.propagate struct;
  pure r

private def expandStructInstExpectedType (stx : Syntax) : MacroM (Option Syntax) :=
let expectedArg := stx.getArg 4;
if expectedArg.isNone then pure none
else
  let expected := expectedArg.getArg 1;
  let stxNew   := stx.setArg 4 mkNullNode;
  `(($stxNew : $expected))

@[builtinTermElab structInst] def elabStructInst : TermElab :=
fun stx expectedType? => do
  stxNew? ← liftMacroM $ expandStructInstExpectedType stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  | none        => do
    stxNew? ← expandNonAtomicExplicitSource stx;
    match stxNew? with
    | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | none => do
      sourceView ← getStructSource stx;
      modifyOp?  ← isModifyOp? stx;
      match modifyOp?, sourceView with
      | some modifyOp, Source.explicit source _ => elabModifyOp stx modifyOp source expectedType?
      | some _,        _                        => throwError stx ("invalid {...} notation, explicit source is required when using '[<index>] := <value>'")
      | _,             _                        => elabStructInstAux stx expectedType? sourceView

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.struct;
pure ()

end StructInst
end Term
end Elab
end Lean
