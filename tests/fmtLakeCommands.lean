import Lake

/-!
Tests for the formatters of the commands that Lake declares outside of its user-facing DSL: the
`configuration` command together with its fields (`fmtConfigDecl`, `fmtConfigField`), the module
glob notations `Mod.*` and `Mod.+` (`fmtGlobAndSubmodules`, `fmtGlobSubmodules`), the `family_def`
command (`fmtFamilyDef`), the opaque forward declaration commands `nonempty_type` and
`hydrate_opaque_type` (`fmtNonemptyTypeCmd`, `fmtHydrateOpaqueTypeCmd`) and the build data
commands `data_type`, `builtin_facet`, `facet_data`, `custom_data`, `package_data`, `module_data`
and `library_data` (`fmtDataTypeDecl`, `fmtBuiltinFacetCommand`, `fmtFacetDataDecl`,
`fmtCustomDataDecl`, `fmtPackageDataDecl`, `fmtModuleDataDecl`, `fmtLibraryDataDecl`). Every
section contains forms that fit on one line, forms that exceed the 100 column soft width and forms
with and without each optional component.

Elaboration of this file fails in many places on purpose: the commands under test declare axioms,
instances and facets for made-up families and target namespaces, which do not resolve.
-/

open Lake System Lean

configuration EmptyConfig where

configuration LinterConfig where
  /-- Whether the linter runs as part of the regular build. -/
  enabled : Bool := true
  linters : Array Name := #[]

configuration ScriptConfig :=
  /-- The documentation string shown by `lake script doc`. -/
  doc : String := ""
  deprecated : Bool := false

configuration TraceConfig where
  mk ::
  inputHash : UInt64 := 0
  depHash : UInt64 := 0
  deriving Inhabited, Repr

public configuration ArtifactConfig (name : Name) extends LinterConfig where
  /-- The directory into which the artifact is written. -/
  outDir : FilePath := "."
  /-- The file name of the artifact. Defaults to the mangled name of the target. -/
  fileName : String := name.toString
  cacheServices @ service, services, cache_service : Array String := #[]

public configuration CachedArtifactConfig (packageName : Name) (targetName : Name) extends ArtifactConfig, TraceConfig, LinterConfig, ScriptConfig where
  /--
  The name under which the artifact is uploaded to the cache.
  Defaults to the mangled name of the package and the target.
  -/
  cacheKey @ cache_key, key, cacheName, cache_name, artifactCacheKey : String := s!"{packageName}-{targetName}"
  /-- Compute the name of the shared library of `platform` from the library's `baseName`. -/
  sharedLibName (platform : String) (baseName : String) : String := s!"lib{baseName}.so"
  postUpdateHooks : Array (Package → LogIO PUnit) := #[]
  transitiveArtifactDependencyClosure : Std.HashMap Name (Array (Name × FilePath × BuildTrace)) := {}

private configuration InternalConfig (name : Name) : Type where
  ref : Name := name

def libGlobs : Array Glob := #[`Lake.Config.*, `Lake.Build.+, Glob.one `Lake.Util]

def workspaceGlobs : Array Glob :=
  #[`Lake.Config.*, `Lake.Build.*, `Lake.Util.*, `Lake.Toml.*, `Lake.CLI.*, `Lake.Load.*, `Lake.DSL.+]

def coveredByGlobs (mod : Name) : Bool :=
  Glob.matches mod `Lake.Config.* || Glob.matches mod `Lake.Build.Module.Facets.+

opaque ArtifactFam (idx : Name) : Type
opaque TargetFam (idx : Name × Name) : Type

family_def olean : ArtifactFam `olean := FilePath

/-- The trace of the C file that was compiled for a module. -/
family_def compiledCTrace : ArtifactFam `Lake.Build.Module.compiledCTrace := BuildTrace

family_def transitiveImportGraph : ArtifactFam `Lake.Build.Module.transitiveImportGraph := Std.HashMap Name (Array Name)

family_def externLibArtifacts : TargetFam (`Lake.Build.ExternLib, `Lake.Build.ExternLib.artifacts) := Array FilePath

nonempty_type OpaqueBuildJob

/-- An opaque reference to the build store of a package's target. -/
public nonempty_type OpaqueBuildStore (packageName : Name) (targetName : Name)

private nonempty_type OpaqueRecursiveBuildContext (packageName : Name) (libraryName : Name) (moduleName : Name) (facetName : Name)

hydrate_opaque_type OpaqueBuildJob BuildJob

public hydrate_opaque_type OpaqueBuildStore BuildStore packageName targetName

private hydrate_opaque_type OpaqueRecursiveBuildContext RecursiveBuildContext packageName libraryName moduleName facetName

data_type artifact : FilePath

/-- The cache of every module artifact that the workspace has produced so far. -/
data_type module_cache : Std.HashMap Name (Array FilePath)

data_type transitive_module_dependency_cache : Std.HashMap Name (Array (Name × FilePath × BuildTrace))

builtin_facet olean : Module => FilePath

/-- The transitive imports of a module, including the module itself. -/
builtin_facet transImportsWithSelf : Module => Array Module

builtin_facet serverOlean @ oleanServer : Module => FilePath

builtin_facet precompiledTransitiveImportDynlibs @ precompiledTransImportDynlibs : LeanLib => Array Dynlib

facet_data module olean : FilePath

/-- The direct dependencies of a package. -/
facet_data package deps : Array Package

facet_data lean_lib precompiledDynlibsOfTheTransitiveImportClosure : Array (Name × Dynlib × BuildTrace)

package_data deps : Array Package

/-- The modules of a package that are built by default. -/
module_data olean : FilePath

module_data transitiveImportsWithPrecompiledDynlibs : Array (Name × Dynlib × FilePath × BuildTrace)

library_data static : FilePath

library_data staticExportOfEveryTransitivelyPrecompiledModule : Array (Name × FilePath)

custom_data myPackage myTarget : Array FilePath

/-- The artifacts that the `docs` target of the `mathlib` package produces. -/
custom_data mathlib docsWithTransitiveDependenciesAndTraces : Array (Name × FilePath × BuildTrace)
