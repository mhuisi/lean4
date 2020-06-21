/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper functions for retrieving structure information.
-/
prelude
import Lean.Environment
import Lean.ProjFns

namespace Lean

/--
  Return true iff `constName` is the a non-recursive inductive
  datatype that has only one constructor. -/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
match env.find? constName with
| some (ConstantInfo.inductInfo { isRec := false, ctors := [ctor], .. }) => true
| _ => false

/-- We mark subobject fields by prefixing them with "_" in the structure's intro rule. -/
def mkInternalSubobjectFieldName (fieldName : Name) : Name :=
fieldName.appendBefore "_"

def isInternalSubobjectFieldName : Name → Bool
| Name.str _ s _ => s.length > 0 && s.get 0 == '_'
| _              => false

def deinternalizeFieldName : Name → Name
| n@(Name.str p s _) => if s.length > 0 && s.get 0 == '_' then mkNameStr p (s.drop 1) else n
| n                  => n

def getStructureCtor (env : Environment) (constName : Name) : ConstructorVal :=
match env.find? constName with
| some (ConstantInfo.inductInfo { nparams := nparams, isRec := false, ctors := [ctorName], .. }) =>
  match env.find? ctorName with
  | some (ConstantInfo.ctorInfo val) => val
  | _ => panic! "ill-formed environment"
| _ => panic! "structure expected"

private def getStructureFieldsAux (nparams : Nat) : Nat → Expr → Array Name → Array Name
| i, Expr.forallE n d b _, fieldNames =>
  if i < nparams then
    getStructureFieldsAux (i+1) b fieldNames
  else
    getStructureFieldsAux (i+1) b (fieldNames.push $ deinternalizeFieldName n)
| _, _, fieldNames => fieldNames

def getStructureFields (env : Environment) (structName : Name) : Array Name :=
let ctor := getStructureCtor env structName;
getStructureFieldsAux ctor.nparams 0 ctor.type #[]

private def isSubobjectFieldAux (nparams : Nat) (target : Name) : Nat → Expr → Option Name
| i, Expr.forallE n d b _ =>
  if i < nparams then
    isSubobjectFieldAux (i+1) b
  else if n == target then
    match d.getAppFn with
    | Expr.const parentStructName _ _ => some parentStructName
    | _ => panic! "ill-formed structure"
  else
    isSubobjectFieldAux (i+1) b
| _, _ => none

/-- If `fieldName` represents the relation to a parent structure `S`, return `S` -/
def isSubobjectField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
let ctor := getStructureCtor env structName;
isSubobjectFieldAux ctor.nparams (mkInternalSubobjectFieldName fieldName) 0 ctor.type

/-- Return immediate parent structures -/
def getParentStructures (env : Environment) (structName : Name) : Array Name :=
let fieldNames := getStructureFields env structName;
fieldNames.foldl
  (fun (acc : Array Name) fieldName =>
    match isSubobjectField? env structName fieldName with
    | some parentStructName => acc.push parentStructName
    | none                  => acc)
  #[]

/-- `findField? env S fname`. If `fname` is defined in a parent `S'` of `S`, return `S'` -/
partial def findField? (env : Environment) : Name → Name → Option Name
| structName, fieldName =>
  if (getStructureFields env structName).contains fieldName then
    some structName
  else
    (getParentStructures env structName).findSome? $ fun parentStructName => findField? parentStructName fieldName

private partial def getStructureFieldsFlattenedAux (env : Environment) : Name → Array Name → Array Name
| structName, fullNames =>
  (getStructureFields env structName).foldl
    (fun (fullNames : Array Name) (fieldName : Name) =>
      let fullNames := fullNames.push fieldName;
      match isSubobjectField? env structName fieldName with
      | some parentStructName => getStructureFieldsFlattenedAux parentStructName fullNames
      | none                  => fullNames)
    fullNames

def getStructureFieldsFlattened (env : Environment) (structName : Name) : Array Name :=
getStructureFieldsFlattenedAux env structName #[]

private def hasProjFn (env : Environment) (structName : Name) (nparams : Nat) : Nat → Expr → Bool
| i, Expr.forallE n d b _ =>
  if i < nparams then
    hasProjFn (i+1) b
  else
    let fullFieldName := structName ++ deinternalizeFieldName n;
    env.isProjectionFn fullFieldName
| _, _ => false

/--
  Return true if `constName` is the name of an inductive datatype
  created using the `structure` or `class` commands.

  We perform the check by testing whether auxiliary projection functions
  have been created. -/
def isStructure (env : Environment) (constName : Name) : Bool :=
if isStructureLike env constName then
  let ctor := getStructureCtor env constName;
  hasProjFn env constName ctor.nparams 0 ctor.type
else
  false

partial def getPathToBaseStructureAux (env : Environment) (baseStructName : Name) : Name → List Name → Option (List Name)
| structName, path =>
  if baseStructName == structName then
    some path.reverse
  else
    let fieldNames := getStructureFields env structName;
    fieldNames.findSome? $ fun fieldName =>
      match isSubobjectField? env structName fieldName with
      | none                  => none
      | some parentStructName => getPathToBaseStructureAux parentStructName ((structName ++ fieldName) :: path)

/--
  If `baseStructName` is an ancestor structure for `structName`, then return a sequence of projection functions
  to go from `structName` to `baseStructName`. -/
def getPathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
getPathToBaseStructureAux env baseStructName structName []

end Lean
