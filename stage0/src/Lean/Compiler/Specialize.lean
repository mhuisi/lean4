/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes
import Lean.Compiler.Util

namespace Lean
namespace Compiler

inductive SpecializeAttributeKind
| specialize | nospecialize

namespace SpecializeAttributeKind

instance : Inhabited SpecializeAttributeKind := ⟨SpecializeAttributeKind.specialize⟩

protected def beq : SpecializeAttributeKind → SpecializeAttributeKind → Bool
| specialize, specialize => true
| nospecialize, nospecialize => true
| _, _ => false

instance : HasBeq SpecializeAttributeKind := ⟨SpecializeAttributeKind.beq⟩

end SpecializeAttributeKind

def mkSpecializeAttrs : IO (EnumAttributes SpecializeAttributeKind) :=
registerEnumAttributes `specializeAttrs
  [(`specialize, "mark definition to always be inlined", SpecializeAttributeKind.specialize),
   (`nospecialize, "mark definition to never be inlined", SpecializeAttributeKind.nospecialize) ]
  /- TODO: fix the following hack.
     We need to use the following hack because the equation compiler generates auxiliary
     definitions that are compiled before we even finish the elaboration of the current command.
     So, if the current command is a `@[specialize] def foo ...`, we must set the attribute `[specialize]`
     before we start elaboration, otherwise when we compile the auxiliary definitions we will not be
     able to test whether `@[specialize]` has been set or not.
     In the new equation compiler we should pass all attributes and allow it to apply them to auxiliary definitions.
     In the current implementation, we workaround this issue by using functions such as `hasSpecializeAttrAux`.
   -/
  (fun env declName _ => Except.ok ())
  AttributeApplicationTime.beforeElaboration

@[init mkSpecializeAttrs]
constant specializeAttrs : EnumAttributes SpecializeAttributeKind := arbitrary _

private partial def hasSpecializeAttrAux (env : Environment) (kind : SpecializeAttributeKind) : Name → Bool
| n => match specializeAttrs.getValue env n with
  | some k => kind == k
  | none   => if n.isInternal then hasSpecializeAttrAux n.getPrefix else false

@[export lean_has_specialize_attribute]
def hasSpecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.specialize n

@[export lean_has_nospecialize_attribute]
def hasNospecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.nospecialize n

inductive SpecArgKind
| fixed
| fixedNeutral -- computationally neutral
| fixedHO      -- higher order
| fixedInst    -- type class instance
| other

structure SpecInfo :=
(mutualDecls : List Name) (argKinds : SpecArgKind)

structure SpecState :=
(specInfo : SMap Name SpecInfo := {})
(cache    : SMap Expr Name := {})

inductive SpecEntry
| info (name : Name) (info : SpecInfo)
| cache (key : Expr) (fn : Name)

namespace SpecState

instance : Inhabited SpecState := ⟨{}⟩

def addEntry (s : SpecState) (e : SpecEntry) : SpecState :=
match e with
| SpecEntry.info name info => { s with specInfo := s.specInfo.insert name info }
| SpecEntry.cache key fn   => { s with cache    := s.cache.insert key fn }

def switch : SpecState → SpecState
| ⟨m₁, m₂⟩ => ⟨m₁.switch, m₂.switch⟩

end SpecState

def mkSpecExtension : IO (SimplePersistentEnvExtension SpecEntry SpecState) :=
registerSimplePersistentEnvExtension {
  name          := `specialize,
  addEntryFn    := SpecState.addEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries SpecState.addEntry {} es).switch
}

@[init mkSpecExtension]
constant specExtension : SimplePersistentEnvExtension SpecEntry SpecState := arbitrary _

@[export lean_add_specialization_info]
def addSpecializationInfo (env : Environment) (fn : Name) (info : SpecInfo) : Environment :=
specExtension.addEntry env (SpecEntry.info fn info)

@[export lean_get_specialization_info]
def getSpecializationInfo (env : Environment) (fn : Name) : Option SpecInfo :=
(specExtension.getState env).specInfo.find? fn

@[export lean_cache_specialization]
def cacheSpecialization (env : Environment) (e : Expr) (fn : Name) : Environment :=
specExtension.addEntry env (SpecEntry.cache e fn)

@[export lean_get_cached_specialization]
def getCachedSpecialization (env : Environment) (e : Expr) : Option Name :=
(specExtension.getState env).cache.find? e

end Compiler
end Lean
