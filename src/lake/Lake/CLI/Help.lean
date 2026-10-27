/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Init.Data.ToString
import Lake.Version

namespace Lake

public def usage :=
  uiVersionString ++ "\n\nUSAGE:\
    \n  lake [OPTIONS] <COMMAND>\
    \n\
    \nCOMMANDS:\
    \n  new <name> <temp>     create a Lean package in a new directory\
    \n  init <name> <temp>    create a Lean package in the current directory\
    \n  build <targets>...    build targets\
    \n  query <targets>...    build targets and output results\
    \n  exe <exe> <args>...   build an exe and run it in Lake's environment\
    \n  samply <exe>          profile an exe with samply and demangle Lean names\
    \n  check-build           check if any default build targets are configured\
    \n  test                  test the package using the configured test driver\
    \n  check-test            check if there is a properly configured test driver\
    \n  lint                  lint the package\
    \n  check-lint            check if there is a properly configured lint driver\
    \n  clean                 remove build outputs\
    \n  shake                 minimize imports in source files\
    \n  comparator            judge a solution against a challenge\
    \n  check                 check this project against external checker(s)\
    \n  env <cmd> <args>...   execute a command in Lake's environment\
    \n  lean <file>           elaborate a Lean file in Lake's context\
    \n  update                update dependencies and save them to the manifest\
    \n  pack                  pack build artifacts into an archive for distribution\
    \n  unpack                unpack build artifacts from an distributed archive\
    \n  upload <tag>          upload build artifacts to a GitHub release\
    \n  cache                 manage the Lake cache\
    \n  script                manage and run workspace scripts\
    \n  scripts               shorthand for `lake script list`\
    \n  run <script>          shorthand for `lake script run`\
    \n  translate-config      change language of the package configuration\
    \n  serve                 start the Lean language server\
    \n\
    \nBASIC OPTIONS:\
    \n  --version             print version and exit\
    \n  --help, -h            print help of the program or a command and exit\
    \n  --dir, -d=file        use the package configuration in a specific directory\
    \n  --file, -f=file       use a specific file for the package configuration\
    \n  -K key[=value]        set the configuration file option named key\
    \n  --old                 only rebuild modified modules (ignore transitive deps)\
    \n  --rehash, -H          hash all files for traces (do not trust `.hash` files)\
    \n  --update              update dependencies on load (e.g., before a build)\
    \n  --packages=file       JSON file of package entries that override the manifest\
    \n  --reconfigure, -R     elaborate configuration files instead of using OLeans\
    \n  --keep-toolchain      do not update toolchain on workspace update\
    \n  --allow-empty         accept bare builds with no default targets configured\
    \n  --no-build            exit immediately if a build target is not up-to-date\
    \n  --fail-fast           stop scheduling new build jobs after the first required failure\
    \n  --no-cache            build packages locally; do not download build caches\
    \n  --try-cache           attempt to download build caches for supported packages\
    \n  --json, -J            output JSON-formatted results (in `lake query`)\
    \n  --text                output results as plain text (in `lake query`)\
    \n\
    \nOUTPUT OPTIONS:\
    \n  --quiet, -q           hide informational logs and the progress indicator\
    \n  --verbose, -v         show trace logs (command invocations) and built targets\
    \n  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output\
    \n  --log-level=lv        minimum log level to output on success\
    \n                        (levels: trace, info, warning, error)\
    \n  --fail-level=lv       minimum log level to fail a build (default: error)\
    \n  --iofail              fail build if any I/O or other info is logged\
    \n                        (same as --fail-level=info)\
    \n  --wfail               fail build if warnings are logged\
    \n                        (same as --fail-level=warning)\
    \n\
    \n\
    \nSee `lake help <command>` for more information on a specific command."

def newInitHelp :=
  s!"If you are using Lake through Elan (which is standard), you can create a\
    \npackage with a specific Lean version via the `+` option.\
    \n\
    \nThe initial configuration and starter files are based on the template:\
    \n\
    \n  std                   library and executable; default\
    \n  exe                   executable only\
    \n  lib                   library only\
    \n  math-lax              library only with a Mathlib dependency\
    \n  math                  library with Mathlib standards for linting and workflows\
    \n\
    \nTemplates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML\
    \nversion of the configuration file, respectively. The default is TOML."

def helpNew :=
  s!"Create a Lean package in a new directory\
    \n\
    \nUSAGE:\
    \n  lake [+<lean-version>] new <name> [<template>][.<language>]\
    \n\
    \n{newInitHelp}"

def helpInit :=
  s!"Create a Lean package in the current directory\
    \n\
    \nUSAGE:\
    \n  lake [+<lean-version>] init [<name>] [<template>][.<language>]\
    \n\
    \n{newInitHelp}\
    \n\
    \nYou can create a package with current directory's name via `lake init .`\
    \nor a bare `lake init`."

def helpBuild :=
  "Build targets\
    \n\
    \nUSAGE:\
    \n  lake build [<targets>...] [-o <mappings>] [--package <name>]\
    \n\
    \nA target is specified with a string of the form:\
    \n\
    \n  [@[<package>]/][<target>|[+]<module>][:<facet>]\
    \n\
    \nYou can also use the source path of a module as a target. For example,\
    \n\
    \n  lake build Foo/Bar.lean:o\
    \n\
    \nwill build the Lean module (within the workspace) whose source file is\
    \n`Foo/Bar.lean` and compile the generated C file into a native object file.\
    \n\
    \nThe `@` and `+` markers can be used to disambiguate packages and modules\
    \nfrom file paths or other kinds of targets (e.g., executables or libraries).\
    \n\
    \nLIBRARY FACETS:         build the library's ...\
    \n  elabArts              elaboration artifacts (*.olean, *.ilean files)\
    \n  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)\
    \n  static                static artifact (*.a file)\
    \n  shared                shared artifact (*.so, *.dll, or *.dylib file)\
    \n\
    \nMODULE FACETS:          build the module's ...\
    \n  deps                  dependencies (e.g., imports, shared libraries, etc.)\
    \n  elabArts              elaboration artifacts (*.olean, *.ilean files)\
    \n  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)\
    \n  olean                 OLean (binary blob of Lean data for importers)\
    \n  ilean                 ILean (binary blob of metadata for the Lean LSP server)\
    \n  c                     compiled C file\
    \n  bc                    compiled LLVM bitcode file\
    \n  c.o                   compiled object file (of its C file)\
    \n  bc.o                  compiled object file (of its LLVM bitcode file)\
    \n  o                     compiled object file (of its configured backend)\
    \n  dynlib                shared library (e.g., for `--load-dynlib`)\
    \n\
    \nTARGET EXAMPLES:        build the ...\
    \n  a                     default facet(s) of target `a`\
    \n  @a                    default target(s) of package `a`\
    \n  +A                    default facet(s) of module `A`\
    \n  @/a                   default facet(s) of target `a` of the root package\
    \n  @a/b                  default facet(s) of target `b` of package `a`\
    \n  @a/+A:c               C file of module `A` of package `a`\
    \n  :foo                  facet `foo` of the root package\
    \n\
    \nA bare `lake build` command will build the default target(s) of the root\
    \npackage. Package dependencies are not updated during a build.\
    \n\
    \nWith the Lake cache enabled, Lake can track the targets the build covers\
    \n(both those up-to-date and those newly built) and write the input-to-outputs\
    \nmappings of each to a file specified by the `-o` option. By default, with `-o`,\
    \nLake will track the targets of the root package, use `--package` to select a\
    \ndifferent one. These mappings can then be used to upload the build artifacts\
    \nto a remote cache with `lake cache put`. This will only include the artifacts\
    \nfrom the covered targets. Other targets in the package will not be tracked."

def helpQuery :=
  "Build targets and output results\
    \n\
    \nUSAGE:\
    \n  lake query [<targets>...]\
    \n\
    \nBuilds a set of targets, reporting progress on standard error and outputting\
    \nthe results on standard out. Target results are output in the same order they\
    \nare listed and end with a newline. If `--json` is set, results are formatted as\
    \nJSON. Otherwise, they are printed as raw strings. Targets which do not have\
    \noutput configured will be printed as an empty string or `null`.\
    \n\
    \nSee `lake help build` for information on and examples of targets."

def helpCheckBuild :=
  "Check if any default build targets are configured\
    \n\
    \nUSAGE:\
    \n  lake check-build\
    \n\
    \nExits with code 0 if the workspace's root package has any\
    \ndefault targets configured. Errors (with code 1) otherwise.\
    \n\
    \nDoes NOT verify that the configured default targets are valid.\
    \nIt merely verifies that some are specified.\n"

def helpUpdate :=
  "Update dependencies and save them to the manifest\
    \n\
    \nUSAGE:\
    \n  lake update [<package>...]\
    \n\
    \nALIAS: lake upgrade\
    \n\
    \nUpdates the Lake package manifest (i.e., `lake-manifest.json`),\
    \ndownloading and upgrading packages as needed. For each new (transitive) git\
    \ndependency, the appropriate commit is cloned into a subdirectory of\
    \n`packagesDir`. No copy is made of local dependencies.\
    \n\
    \nIf a set of packages are specified, said dependencies are upgraded to\
    \nthe latest version compatible with the package's configuration (or removed if\
    \nremoved from the configuration). If there are dependencies on multiple versions\
    \nof the same package, the version materialized is undefined.\
    \n\
    \nA bare `lake update` will upgrade all dependencies."

def helpTest :=
  "Test the workspace's root package using its configured test driver\
    \n\
    \nUSAGE:\
    \n  lake test [-- <args>...]\
    \n\
    \nA test driver can be configured by either setting the 'testDriver'\
    \npackage configuration option or by tagging a script, executable, or library\
    \n`@[test_driver]`. A definition in a dependency can be used as a test driver\
    \nby using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.\
    \n\
    \nA script test driver will be run with the  package configuration's\
    \n`testDriverArgs` plus the CLI `args`. An executable test driver will be\
    \nbuilt and then run like a script. A library test driver will just be built.\n"

def helpCheckTest :=
  "Check if there is a properly configured test driver\
    \n\
    \nUSAGE:\
    \n  lake check-test\
    \n\
    \nExits with code 0 if the workspace's root package has a properly\
    \nconfigured lint driver. Errors (with code 1) otherwise.\
    \n\
    \nDoes NOT verify that the configured test driver actually exists in the\
    \npackage or its dependencies. It merely verifies that one is specified.\n"

def helpLint :=
  "Lint the workspace's root package\
    \n\
    \nUSAGE:\
    \n  lake lint [OPTIONS] [<MODULE>...] [-- <args>...]\
    \n\
    \nBy default, runs the package's configured lint driver. If `builtinLint` is\
    \nset to `true` in the package configuration, builtin lints also run.\
    \n\
    \nBuiltin linting (`--builtin-lint`, `--builtin-only`, `--linters`,\
    \n`--lint-only`, or `builtinLint = true` in the package configuration) drives a\
    \nbuild of the targeted modules with the requested linter options enabled.\
    \nThe lint driver path on its own does not trigger a build.\
    \n\
    \nWhich environment linters run on a declaration is determined by the linter\
    \noptions in effect when that declaration was built (e.g. via `set_option` in\
    \nthe source, or via `--linters`/`--lint-only` below). Both override those\
    \noptions for the lint build; `--lint-only` additionally restricts the reported\
    \noutput to exactly the linters its spec enables.\
    \n\
    \nPositional `MODULE` arguments narrow only the builtin lints; if omitted,\
    \nthe workspace's default target roots are used. The lint driver is invoked\
    \nwith `lintDriverArgs` from the package config plus any arguments after\
    \n`--`; the `MODULE` list is not passed to it.\
    \n\
    \nOPTIONS:\
    \n  --builtin-lint        run builtin environment and text linters\
    \n  --builtin-only        run only builtin linters, skip the lint driver\
    \n  --linters <spec>      override linter options for the lint build; <spec> is a\
    \n                        comma-separated list of linter option names, each\
    \n                        optionally prefixed with `-` to disable it. A name\
    \n                        beginning with `.` is shorthand for the `linter.`\
    \n                        prefix, so `.foo` means `linter.foo`. E.g.\
    \n                        `--linters=.foo,-linter.bar`. Repeatable; later\
    \n                        entries override earlier ones for the same linter\
    \n  --lint-only <spec>    like `--linters`, but report ONLY the linters the spec\
    \n                        positively enables, suppressing every other linter\
    \n                        (including default-on linters that are not named).\
    \n                        Expands `linter.all` and linter sets. Uses the same\
    \n                        `<spec>` syntax as `--linters`; switching between\
    \n                        `--linters` and `--lint-only` replaces the prior spec\
    \n  --record-exceptions   record each linter warning as a\
    \n                        `set_option <linter> false in` exception by editing the\
    \n                        offending source files in place, silencing the warning\
    \n                        for that declaration. Implies `--builtin-lint`.\
    \n  --code-quality        records each linter warning as a code quality check result\
    \n                        and runs the registered code quality checks.\
    \n                        Setting this flag will skip lint driver.\
    \n  --checks <mods>       comma-separated list of workspace modules providing\
    \n                        package code quality checks; they are imported\
    \n                        alongside each linted module (implies --code-quality)\
    \n\
    \nA lint driver can be configured by either setting the `lintDriver` package\
    \nconfiguration option or by tagging a script or executable `@[lint_driver]`.\
    \nA definition in a dependency can be used as a lint driver by using the\
    \n`<pkg>/<name>` syntax for the 'lintDriver' configuration option.\
    \n\
    \nA script lint driver will be run with the package configuration's\
    \n`lintDriverArgs` plus the CLI `args`. An executable lint driver will be\
    \nbuilt and then run like a script.\n"

def helpCheckLint :=
  "Check if there is a properly configured lint driver\
    \n\
    \nUSAGE:\
    \n  lake check-lint\
    \n\
    \nExits with code 0 if the workspace's root package has a properly\
    \nconfigured lint driver. Errors (with code 1) otherwise.\
    \n\
    \nDoes NOT verify that the configured lint driver actually exists in the\
    \npackage or its dependencies. It merely verifies that one is specified.\n"

def helpPack :=
  "Pack build artifacts into an archive for distribution\
    \n\
    \nUSAGE:\
    \n  lake pack [<file.tgz>]\
    \n\
    \nPacks the root package's `buildDir` into a gzip tar archive using `tar`.\
    \nIf a path for the archive is not specified, creates an archive in the package's\
    \nLake directory (`.lake`) named according to its `buildArchive` setting.\
    \n\
    \nDoes NOT build any artifacts. It just packs the existing ones."

def helpUnpack :=
  "Unpack build artifacts from a distributed archive\
    \n\
    \nUSAGE:\
    \n  lake unpack [<file.tgz>]\
    \n\
    \nUnpack build artifacts from the gzip tar archive `file.tgz` into the root\
    \npackage's `buildDir`. If a path for the archive is not specified, uses the\
    \nthe package's `buildArchive` in its Lake directory (`.lake`)."

def helpUpload :=
  "Upload build artifacts to a GitHub release\
    \n\
    \nUSAGE:\
    \n  lake upload <tag>\
    \n\
    \nPacks the root package's `buildDir` into a `tar.gz` archive using `tar` and\
    \nthen uploads the asset to the pre-existing GitHub release `tag` using `gh`."

def helpClean :=
  "Remove build outputs\
    \n\
    \nUSAGE:\
    \n  lake clean [<package>...]\
    \n\
    \nIf no package is specified, deletes the build directories of every package in\
    \nthe workspace. Otherwise, just deletes those of the specified packages."

def helpShake :=
  "Minimize imports in Lean source files\
    \n\
    \nUSAGE:\
    \n  lake shake [OPTIONS] [<MODULE>...]\
    \n\
    \nChecks the current project for unused imports by analyzing generated `.olean`\
    \nfiles to deduce required imports and ensuring that every import contributes\
    \nsome constant or other elaboration dependency.\
    \n\
    \nARGUMENTS:\
    \n  <MODULE>              A module path like `Mathlib`. All files transitively\
    \n                        reachable from the provided module(s) will be checked.\
    \n                        If not specified, uses the package's default targets.\
    \n\
    \nOPTIONS:\
    \n  --force               Skip the `lake build --no-build` sanity check\
    \n  --keep-implied        Preserve imports implied by other imports\
    \n  --keep-prefix         Prefer parent module imports over specific submodules\
    \n  --keep-public         Preserve all `public` imports for API stability\
    \n  --add-public          Add new imports as `public` if they were in the\
    \n                        original public closure\
    \n  --add-downstream <MODULE>\
    \n                        Add the module as an `import` to every checked\
    \n                        module that does not reach it yet, except where\
    \n                        that would create an import cycle\
    \n  --add-public-downstream <MODULE>\
    \n                        Like `--add-downstream`, but add the module as a\
    \n                        `public import` wherever it is not reached through\
    \n                        public imports yet. As these are passed on to\
    \n                        importing modules, this adds far fewer imports.\
    \n                        Only one of these two options can be used, once\
    \n  --explain             Show which constants require each import\
    \n  --fix                 Apply suggested fixes directly to source files\
    \n  --gh-style            Output in GitHub problem matcher format\
    \n\
    \nANNOTATIONS:\
    \n  Source files can contain special comments to control shake behavior:\
    \n\
    \n  * `module -- shake: keep-downstream`\
    \n    Preserves this module in all downstream modules\
    \n\
    \n  * `module -- shake: keep-all`\
    \n    Preserves all existing imports in this module\
    \n\
    \n  * `import X -- shake: keep`\
    \n    Preserves this specific import"

def helpComparator :=
  "Judge a solution against a challenge\
    \n\
    \nUSAGE:\
    \n  lake comparator [--config <FILE>] [--challenge-from-export <FILE>]\
    \n                  [--solution-from-export <FILE>] [--paranoid]\
    \n                  [--inadvisably-no-sandbox]\
    \n\
    \nEstablishes that every named theorem in the solution proves the same statement\
    \nas the challenge, uses no axiom outside the permitted list, and is accepted by\
    \nthe kernel.\
    \n\
    \nThe project is untrusted input: its configuration is evaluated, and its code\
    \nbuilt and exported, inside a `bwrap` sandbox, and none of its `.olean` files\
    \nis ever loaded into Lake's own address space. `bubblewrap` is required, and\
    \nneeds either unprivileged user namespaces or to be installed setuid root.\
    \n\
    \nThe project has to carry a `lake-manifest.json`, because dependencies are\
    \nresolved inside the sandbox and it cannot write to the project directory.\
    \nBuilding the project once, before distributing it, is enough to write one.\
    \n\
    \nOPTIONS:\
    \n  --config=<file>            JSON file describing the challenge (see below)\
    \n                             (default: `comparator.json` in the current\
    \n                             directory)\
    \n  --challenge-from-export=<file>\
    \n                             judge this export as the challenge, instead of\
    \n                             building and exporting `challenge_module`\
    \n  --solution-from-export=<file>\
    \n                             judge this export as the solution, instead of\
    \n                             building and exporting `solution_module`\
    \n  --paranoid                 also run all external checkers bundled with Lean\
    \n                             besides Lean's own kernel: `leanchecker-paranoid`,\
    \n                             `lean4lean`, `nanoda`, `con-leche` and `con-ron`\
    \n  --inadvisably-no-sandbox   disable the built-in sandbox. This can compromise\
    \n                             the result fully and is only advised for expert\
    \n                             users.\
    \n\
    \nCONFIGURATION:\
    \n  The challenge author writes the file and distributes it with the project, so\
    \n  that a solver need only point `lake comparator` at it:\
    \n\
    \n  {\
    \n    \"challenge_module\": \"Challenge\",\
    \n    \"solution_module\": \"Solution\",\
    \n    \"theorem_names\": [\"imo2024_p1\"],\
    \n    \"definition_names\": [],\
    \n    \"permitted_axioms\": [\"propext\", \"Quot.sound\", \"Classical.choice\"],\
    \n    \"external_kernels\": {\"nanoda\": [\"nanoda_bin\"]}\
    \n  }\
    \n\
    \n  `challenge_module`, `solution_module`, `theorem_names` and\
    \n  `permitted_axioms` are required; the rest may be omitted.\
    \n  `definition_names` lists the challenge's definition holes, each of which the\
    \n  challenge has to define as `sorry`.\
    \n  `permitted_axioms` is deliberately not defaulted: it is what the verdict\
    \n  means, so the challenge author states it. The three above are the ones\
    \n  `#print axioms` treats as a clean proof.\
    \n\
    \n  `external_kernels` names additional checkers to run over the export, each as\
    \n  the command to execute; the solution must satisfy every one of them as well\
    \n  as Lean's own kernel. `enable_nanoda: true` is still accepted and is\
    \n  equivalent to a \"nanoda\" entry of [\"nanoda_bin\"]; name the command in\
    \n  `external_kernels` instead to run it from elsewhere.\
    \n\
    \nEXIT CODES:\
    \n  0                     accepted\
    \n  1                     rejected: statement mismatch, forbidden axiom, kernel\
    \n                        rejection, or a build that did not succeed\
    \n  2                     could not start: `bwrap` or the manifest is missing,\
    \n                        or the configuration is missing, unreadable or\
    \n                        malformed\
    \n\
    \nEXPORTS:\
    \n  The `--*-from-export` options take an NDJSON export as generated by\
    \n  `leanexport` instead of building and exporting either the challenge or the\
    \n  solution. Note that this option does not check that the provided export\
    \n  matches the challenge or solution in the project this command is being run\
    \n  in. This is useful for several scenarios:\
    \n  - Using export files built in virtual machines for extra isolation.\
    \n  - Using export files built by third parties, e.g. because they require\
    \n    extensive computational resources to generate.\
    \n  - Using export files generated through means other than a standard\
    \n    `lake build`.\
    \n\
    \nENVIRONMENT:\
    \n  COMPARATOR_BWRAP      sandbox executable (default: `bwrap` on PATH)\
    \n\
    \n  The exporter is always the `leanexport` of this toolchain, and deliberately\
    \n  not configurable: the export format has to match the compiler that produced\
    \n  the `.olean` files being exported.\
    \n\
    \nHARDENING:\
    \n  `comparator` uses `bwrap` for sandboxing. `/` is bound read-only and the home directories \
    are then\
    \n  covered, so the code being judged builds against the system it expects and reads none of \
    the\
    \n  invoking user's files. Only `.lake` is writable. Only dependency resolution has a network, \
    because\
    \n  it has to fetch git dependencies; the build, the export and any external kernels run in an \
    empty\
    \n  network namespace."

def helpCheck :=
  "Check this project against external checker(s)\
    \n\
    \nUSAGE:\
    \n  lake check [--from-export <FILE>] [--paranoid] [--inadvisably-no-sandbox]\
    \n\
    \nBuilds the default build targets, exports them, and replays the result through\
    \nthe kernel, erroring on any use of non-standard axioms.\
    \n\
    \nThe project is untrusted input: its configuration is evaluated, and its code\
    \nbuilt and exported, inside a `bwrap` sandbox, and none of its `.olean` files\
    \nis ever loaded into Lake's own address space. `bubblewrap` is required, and\
    \nneeds either unprivileged user namespaces or to be installed setuid root.\
    \n\
    \nThe project has to carry a `lake-manifest.json`, because dependencies are\
    \nresolved inside the sandbox and it cannot write to the project directory.\
    \nBuilding the project once is enough to write one.\
    \n\
    \nOPTIONS:\
    \n  --from-export=<file>       check this export, instead of building and\
    \n                             exporting the project (see below)\
    \n  --paranoid                 also run all external checkers bundled with Lean\
    \n                             besides Lean's own kernel: `leanchecker-paranoid`,\
    \n                             `lean4lean`, `nanoda`, `con-leche` and `con-ron`\
    \n  --inadvisably-no-sandbox   disable the built-in sandbox. This can compromise\
    \n                             the result fully and is only advised for expert\
    \n                             users.\
    \n\
    \nEXPORTS:\
    \n  The `--from-export` option takes an NDJSON export as generated by\
    \n  `leanexport` instead of building and exporting the entire project. Note that\
    \n  using this option only establishes that the export file is accepted and\
    \n  nothing about the project this command is being run in. This is useful for\
    \n  several scenarios:\
    \n  - Using export files built in virtual machines for extra isolation.\
    \n  - Using export files built by third parties, e.g. because they require\
    \n    extensive computational resources to generate.\
    \n  - Using export files generated through means other than a standard\
    \n    `lake build`.\
    \n\
    \nEXIT CODES:\
    \n  0                     every selected checker accepts the project and it uses\
    \n                        only the permitted axioms\
    \n  1                     a checker rejects it, an axiom is not permitted, or a\
    \n                        build did not succeed\
    \n  2                     could not start: `bwrap` is missing, the project has\
    \n                        no `lake-manifest.json`, or it has no default targets\
    \n\
    \nENVIRONMENT:\
    \n  COMPARATOR_BWRAP      sandbox executable (default: `bwrap` on PATH)\
    \n\
    \n  The exporter is always the `leanexport` of this toolchain, and deliberately\
    \n  not configurable: the export format has to match the compiler that produced\
    \n  the `.olean` files being exported.\
    \n\
    \nHARDENING:\
    \n  The sandbox bounds writes and the network exactly as `lake comparator`'s\
    \n  does, and its limits apply here too. See the HARDENING section of\
    \n  `lake help comparator`.\
    \n\
    \nSee `lake help comparator` to judge a solution against a challenge instead."

def helpCacheCli :=
  "Manage the Lake cache\
    \n\
    \nUSAGE:\
    \n  lake cache <COMMAND>\
    \n\
    \nCOMMANDS:\
    \n  get [<mappings>]      download build outputs into the local Lake cache\
    \n  put <mappings>        upload build outputs to a remote cache\
    \n  add <mappings>        add input-to-output mappings to the Lake cache\
    \n  clean                 removes ALL from the local Lake cache\
    \n  services              print configured remote cache services\
    \n\
    \nSTAGING COMMANDS:\
    \n  stage <map> <dir>     copy build outputs from the cache to a directory\
    \n  unstage <dir>         cache build outputs from a staging directory\
    \n  put-staged <dir>      upload build outputs from a staging directory\
    \n\
    \nSee `lake cache help <command>` for more information on a specific command."

def helpCacheGet :=
  "Download build outputs from a remote service into the Lake cache\
    \n\
    \nUSAGE:\
    \n  lake cache get [<mappings>]\
    \n\
    \nOPTIONS:\
    \n  --max-revs=<n>                  backtrack up to n revisions (default: 100)\
    \n  --rev=<commit-hash>             lookup artifacts only for set revision\
    \n  --package=<name>                fetch outputs for set package\
    \n  --service=<name>                fetch outputs from set cache service\
    \n  --repo=<github-repo>            GitHub repository of the package or its fork\
    \n  --platform=<target-triple>      with Reservoir or --repo, set the platform\
    \n  --toolchain=<name>              with Reservoir or --repo, set the toolchain\
    \n  --scope=<remote-scope>          verbatim scope for a custom endpoint\
    \n  --mappings-only                 only download mappings, delay artifacts\
    \n  --force-download                redownload existing files\
    \n\
    \nDownloads build outputs for packages in the workspace from a remote cache\
    \nservice. The cache service used can be specified via the `--service` option.\
    \nOtherwise, Lake will use the configured default or, if none, Reservoir. See\
    \n`lake cache services` for more information on how to configure services.\
    \n\
    \nBy default, Lake will use Reservoir to download outputs for each\
    \ndependency in the workspace (in order). Non-Reservoir dependencies will be\
    \nskipped. If instead an input-to-outputs mappings file, `--scope`, or `--repo`\
    \nis provided, Lake will default to downloading build outputs for the root\
    \npackage. In either case, if `--package` is specified, Lake will switch to\
    \nonly downloading outputs for it.\
    \n\
    \nTo determine what to download, Lake searches for input-to-output mappings for\
    \na given build of a package via the cache service. This mapping is identified\
    \nby a Git revision and prefixed with a scope derived from the package's name,\
    \nGitHub repository, Lean toolchain, and current platform. The exact configuration\
    \ncan be customized using options.\
    \n\
    \nFor Reservoir, setting `--repo` will cause Lake to lookup outputs for the\
    \npackage by a repository name, rather than the package's. This can be used to\
    \ndownload outputs for a fork of the Reservoir package (if such artifacts are\
    \navailable). The `--platform` and `--toolchain` options can be used to download\
    \nartifacts for a different platform/toolchain configuration than Lake detects.\
    \nFor a custom endpoint, the full prefix Lake uses can be set via `--scope`.\
    \n\
    \nIf `--rev` is not set, Lake uses the package's current revision to lookup\
    \nartifacts. If no mappings are found, Lake will backtrack the Git history up to\
    \n`--max-revs`, looking for a revision with mappings. If `--max-revs` is 0, Lake\
    \nwill search the repository's entire history (or as far as Git will allow).\
    \n\
    \nBy default, Lake will download both the input-to-output mappings and the\
    \noutput artifacts for a package. By using `--mappings-only`, Lake will only\
    \ndownload the mappings and delay downloading artifacts until they are needed.\
    \n\
    \nIf a download for an artifact fails or the download process for a whole\
    \npackage fails, Lake will report this and continue on to the next. Once done,\
    \nif any download failed, Lake will exit with a nonzero status code."

def helpCachePut :=
  "Upload build outputs from the Lake cache to a remote service\
    \n\
    \nUSAGE:\
    \n  lake cache put <mappings>\
    \n\
    \nOPTIONS:\
    \n  --package=<name>                upload for set package\
    \n  --service=<name>                upload to set cache service\
    \n  --scope=<remote-scope>          upload under set scope verbatim\
    \n  --repo=<github-repo>            scope w/ repository + toolchain & platform\
    \n  --toolchain=<name>              with --repo, sets the toolchain\
    \n  --platform=<target-triple>      with --repo, sets the platform\
    \n\
    \nUploads the input-to-output mappings contained in the specified file along\
    \nwith the corresponding output artifacts to a remote cache. The cache service\
    \nused can be specified via the `--service` option. If not specified, Lake will\
    \nuse the system default, or error if none is configured. See the help page of\
    \n`lake cache services` for more information on how to configure services.\
    \n\
    \nFiles are uploaded using the AWS Signature Version 4 authentication protocol\
    \nvia `curl`. Thus, the service should generally be an S3-compatible bucket.\
    \nThe authentication key is set via the `LAKE_CACHE_KEY` environment variable.\
    \n\
    \nSince Lake does not currently use cryptographically secure hashes for\
    \nartifacts and outputs, uploads to the cache are prefixed with a scope to\
    \navoid clashes. This is controlled by `--scope` or `--repo`. With `--repo`,\
    \nLake will produce a scope by augmenting the repository with toolchain and\
    \nplatform information as it deems necessary. With `--scope`, Lake will use\
    \nthe specified scope verbatim.\
    \n\
    \nArtifacts are uploaded to the artifact endpoint with a file name derived\
    \nfrom their Lake content hash (and prefixed by the repository or scope).\
    \nThe mappings file is uploaded to the revision endpoint with a file name\
    \nderived from the package's current Git revision (and prefixed by the\
    \nfull scope). As such, the command will warn if the work tree currently\
    \nhas changes."

def helpCacheAdd :=
  "Add input-to-output mappings to the Lake cache\
    \n\
    \nUSAGE:\
    \n  lake cache add <mappings>\
    \n\
    \nOPTIONS:\
    \n  --package=<name>                add mappings to set package\
    \n  --service=<name>                cache service to fetch from on demand\
    \n  --scope=<remote-scope>          the prefix of artifacts within the service\
    \n  --repo=<github-repo>            for Reservoir, a GitHub repository scope\
    \n  --no-overwrite                  do not overwrite existing mappings\
    \n\
    \nReads a list of input-to-output mappings from the provided file and adds\
    \nthem to the local Lake cache. Mappings already in the cache are overwritten\
    \nunless `--no-overwrite` is specified. Mappings are added for the root package\
    \nunless `--package` is specified.\
    \n\
    \nIf `--service` is provided, the output artifacts can then be fetched lazily\
    \nfrom that service during a Lake build. The service must either be `reservoir`\
    \nor be configured through the Lake system configuration (see the help page of\
    \n`lake cache services` for details).\
    \n\
    \nSince Lake does not currently use cryptographically secure hashes for\
    \nartifacts and outputs, artifacts in a cache service are prefixed with a scope\
    \nto avoid clashes. For Reservoir, this scope can either be a package (set via\
    \n`--scope`) or a repository (set via `--repo`). For S3 services, both options\
    \nare synonymous."

def helpCacheStage :=
  "Copy build outputs from the cache to a staging directory\
    \n\
    \nUSAGE:\
    \n  lake cache stage <mappings> <staging-directory> [--force-overwrite]\
    \n\
    \nCreates the staging directory and copies the mappings file to it. Then,\
    \nit copies all artifacts described within the mappings file from the cache to\
    \nthe staging directory. Artifacts in the staging directory are not overwritten\
    \nunless `--force-overwrite` is specified. Errors if any of the artifacts\
    \ndescribed cannot be found in the cache."

def helpCacheUnstage :=
  "Cache build outputs from a staging directory\
    \n\
    \nUSAGE:\
    \n  lake cache unstage <staging-directory> [--force-overwrite]\
    \n\
    \nCopies the mappings and artifacts stored in staging directory (e.g., via\
    \n`lake cache stage`) back into the cache.\
    \n\
    \nReads the mappings file located at `outputs.jsonl` within the staging\
    \ndirectory and writes the mappings to the Lake cache. Then, it copies the\
    \ndescribed artifacts from the staging directory into the cache. Mappings and\
    \nartifacts already in the cache are not overwritten unless `--force-overwrite`\
    \nis specified."

def helpCachePutStaged :=
  "Upload build outputs from a staging directory to a remote service\
    \n\
    \nUSAGE:\
    \n  lake cache put-staged <staging-directory>\
    \n\
    \nOPTIONS:\
    \n  --rev=<commit-hash>             upload for set revision\
    \n  --service=<name>                upload to set cache service\
    \n  --scope=<remote-scope>          upload under set scope verbatim\
    \n  --repo=<github-repo>            scope w/ repository + toolchain & platform\
    \n  --toolchain=<name>              with --repo, set the toolchain\
    \n  --platform=<target-triple>      with --repo, set the platform\
    \n\
    \nWorks like `lake cache put` but uploads outputs from the staging directory\
    \ninstead of the Lake cache.\
    \n\
    \nDoes not configure the workspace and thus does not execute arbitrary user\
    \ncode. However, because of this, the package's platform and toolchain settings\
    \nwill not be automatically detected for `--repo` and must be specified manually\
    \nvia `--platform` and `--toolchain` (if needed). Similarly, the source revision\
    \nthe outputs correspond to must be manually specified via `--rev`."

def helpCacheClean :=
  "Removes ALL files from the local Lake cache\
    \n\
    \nUSAGE:\
    \n  lake cache clean\
    \n\
    \nDeletes the configured Lake cache directory. If a workspace configuration\
    \nexists, this will delete the cache directory it uses. Otherwise, it will\
    \ndelete the default Lake cache directory for the system."

def helpCacheServices :=
  "Print configured remote cache services\
    \n\
    \nUSAGE:\
    \n  lake cache services\
    \n\
    \nPrints the name of each configured remote cache services (one per line).\
    \nAdditional services can be added by modifying the system Lake configuration.\
    \nThe exact location of the this configuration file is system dependent and can\
    \nbe set by `LAKE_CONFIG`, but it is usually located at `~/.lake/config.toml`.\
    \n\
    \nThe configuration of the system cache could look something like the following:\
    \n\
    \n  cache.defaultService = \"my-s3\"\
    \n  cache.defaultUploadService = \"my-s3\"\
    \n\
    \n  [[cache.service]]\
    \n  name = \"my-s3\"\
    \n  kind = \"s3\"\
    \n  artifactEndpoint = \"https://my-s3.com/a0\"\
    \n  revisionEndpoint = \"https://my-s3.com/r0\"\
    \n\
    \nIf no `cache.defaultService` is configured, Lake will use Reservoir by default."

def helpScriptCli :=
  "Manage Lake scripts\
    \n\
    \nUSAGE:\
    \n  lake script <COMMAND>\
    \n\
    \nCOMMANDS:\
    \n  list                  list available scripts\
    \n  run <script>          run a script\
    \n  doc <script>          print the docstring of a given script\
    \n\
    \nSee `lake script help <command>` for more information on a specific command."

def helpScriptList :=
  "List available scripts\
    \n\
    \nUSAGE:\
    \n  lake script list\
    \n\
    \nALIAS: lake scripts\
    \n\
    \nThis command prints the list of all available scripts in the workspace."

def helpScriptRun :=
  "Run a script\
    \n\
    \nUSAGE:\
    \n  lake script run [[<package>/]<script>] [<args>...]\
    \n\
    \nALIAS: lake run\
    \n\
    \nThis command runs the `script` of the workspace (or the specific `package`),\
    \npassing `args` to it.\
    \n\
    \nA bare `lake run` command will run the default script(s) of the root package\
    \n(with no arguments)."

def helpScriptDoc :=
  "Print a script's docstring\
    \n\
    \nUSAGE:\
    \n  lake script doc [<package>/]<script>\
    \n\
    \nPrint the docstring of `script` in the workspace or the specific `package`."

def helpServe :=
  "Start the Lean language server\
    \n\
    \nUSAGE:\
    \n  lake serve [-- <args>...]\
    \n\
    \nRun the language server of the Lean installation (i.e., via `lean --server`)\
    \nwith the package configuration's `moreServerArgs` field and `args`.\n"

def helpEnv :=
  "Execute a command in Lake's environment\
    \n\
    \nUSAGE:\
    \n  lake env [<cmd>] [<args>...]\
    \n\
    \nSpawns a new process executing `cmd` with the given `args` and with\
    \nthe environment set based on the detected Lean/Lake installations and\
    \nthe workspace configuration (if it exists).\
    \n\
    \nSpecifically, this command sets the following environment variables:\
    \n\
    \n  LAKE                  set to the detected Lake executable\
    \n  LAKE_HOME             set to the detected Lake home\
    \n  LEAN_SYSROOT          set to the detected Lean toolchain directory\
    \n  LEAN_AR               set to the detected Lean `ar` binary\
    \n  LEAN_CC               set to the detected `cc` (if not using the bundled one)\
    \n  LEAN_PATH             adds Lake's and the workspace's Lean library dirs\
    \n  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs\
    \n  PATH                  adds Lean's, Lake's, and the workspace's binary dirs\
    \n  PATH                  adds Lean's and the workspace's library dirs (Windows)\
    \n  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)\
    \n  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)\
    \n\
    \nA bare `lake env` will print out the variables set and their values,\
    \nusing the form NAME=VALUE like the POSIX `env` command."

def helpExe :=
  "Build an executable target and run it in Lake's environment\
    \n\
    \nUSAGE:\
    \n  lake exe <exe-target> [<args>...]\
    \n\
    \nALIAS: lake exec\
    \n\
    \nLooks for the executable target in the workspace (see `lake help build` to\
    \nlearn how to specify targets), builds it if it is out of date, and then runs\
    \nit with the given `args` in Lake's environment (see `lake help env` for how\
    \nthe environment is set up)."

def helpSamply :=
  "Profile an executable target with samply and demangle Lean names\
    \n\
    \nUSAGE:\
    \n  lake samply [OPTIONS] <exe-target> [-- [<samply-args>...] [-- <exe-args>...]]\
    \n\
    \nBuilds the executable target, records a CPU profile using samply, symbolicates\
    \nthe raw addresses, demangles Lean compiler names, and writes a Firefox Profiler\
    \nJSON file.\
    \n\
    \nOPTIONS:\
    \n  -o FILE               output path (default: ./profile-demangled.json.gz)\
    \n  --raw                 save the raw profile without serving (default: ./profile-raw.json.gz)\
    \n  --no-serve            write output file and exit without serving it\
    \n\
    \nAnything after `--` is forwarded verbatim to `samply record`. An inner `--`\
    \nseparates samply's own flags from the profiled executable's arguments, e.g.:\
    \n\
    \n  lake samply mergeSort                          # no samply or exe args\
    \n  lake samply mergeSort -- --rate 2000           # only samply args\
    \n  lake samply mergeSort -- -- 10                 # only exe args\
    \n  lake samply mergeSort -- --rate 2000 -- 10     # both\
    \n\
    \nRun `samply record --help` to see samply's flags.\
    \n\
    \nREQUIREMENTS:\
    \n  samply                cargo install samply\
    \n  curl, gzip            standard on most Linux/macOS systems\
    \n\
    \nOpen the output file in Firefox Profiler at https://profiler.firefox.com/from-file/"

def helpLean :=
  "Elaborate a Lean file in the context of the Lake workspace\
    \n\
    \nUSAGE:\
    \n  lake lean <file> [-- <args>...]\
    \n\
    \nBuild the imports of the given file and then runs `lean` on it using\
    \nthe workspace's root package's additional Lean arguments and the given args\
    \n(in that order). The `lean` process is executed in Lake's environment like\
    \n`lake env lean` (see `lake help env` for how the environment is set up)."

def helpTranslateConfig :=
  "Translate a Lake configuration file into a different language\
    \n\
    \nUSAGE:\
    \n  lake translate-config <lang> [<out-file>]\
    \n\
    \nTranslates the loaded package's configuration into another of\
    \nLake's supported configuration languages (i.e., either `lean` or `toml`).\
    \nThe produced file is written to `out-file` or, if not provided, the path of\
    \nthe configuration file with the new language's extension. If the output file\
    \nalready exists, Lake will error.\
    \n\
    \nTranslation is lossy. It does not preserve comments or formatting and\
    \nnon-declarative configuration will be discarded."

public def helpScript : (cmd : String) → String
  | "list" => helpScriptList
  | "run" => helpScriptRun
  | "doc" => helpScriptDoc
  | _ => helpScriptCli

public def helpCache : (cmd : String) → String
  | "get" => helpCacheGet
  | "put" => helpCachePut
  | "add" => helpCacheAdd
  | "stage" => helpCacheStage
  | "unstage" => helpCacheUnstage
  | "put-staged" => helpCachePutStaged
  | "clean" => helpCacheClean
  | "services" => helpCacheServices
  | _ => helpCacheCli

public def help : (cmd : String) → String
  | "new" => helpNew
  | "init" => helpInit
  | "build" => helpBuild
  | "check-build" => helpCheckBuild
  | "query" => helpQuery
  | "update" | "upgrade" => helpUpdate
  | "pack" => helpPack
  | "unpack" => helpUnpack
  | "upload" => helpUpload
  | "cache" => helpCacheCli
  | "test" => helpTest
  | "check-test" => helpCheckTest
  | "lint" => helpLint
  | "check-lint" => helpCheckLint
  | "clean" => helpClean
  | "shake" => helpShake
  | "comparator" => helpComparator
  | "check" => helpCheck
  | "script" => helpScriptCli
  | "scripts" => helpScriptList
  | "run" => helpScriptRun
  | "serve" => helpServe
  | "env" => helpEnv
  | "exe" | "exec" => helpExe
  | "samply" => helpSamply
  | "lean" => helpLean
  | "translate-config" => helpTranslateConfig
  | _ => usage
