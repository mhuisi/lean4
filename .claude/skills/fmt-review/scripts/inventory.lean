import Lean

/-!
Writes the syntax inventory of `Init`, `Std`, `Lean` and `Lake` to a JSON file:

* `decls`: every declaration whose type ends in a parser type (`Parser`, `TrailingParser`,
  `ParserFn`, `ParserDescr`, `TrailingParserDescr`), with its module, line range, a hash of its
  type and value, the parser declarations it uses (`deps`) and the syntax node kinds it defines
  (`kinds`).
* `kinds`: every syntax node kind of the parser extension, with the declarations that define it
  (`owners`), its categories and the formatter that `Lean.Fmt` resolves for it (`null` if there is
  none).
* `fmts`: every formatter declaration that an attribute registers for a kind, with its module,
  line range and the hash of its value.
* `categories` and `tokens`.

Usage (from the repository root):

  build/release/stage1/bin/lean --plugin=build/release/stage1/lib/lean/libLake_shared.so \
    --run .claude/skills/fmt-review/scripts/inventory.lean <out.json>

`lean` does not link Lake, so Lake's builtin formatters only register with the plugin.
-/

open Lean

namespace FmtReview

def parserTypes : List Name :=
  [``Parser.Parser, ``Parser.TrailingParser, ``Parser.ParserFn, ``ParserDescr,
    ``TrailingParserDescr]

def parserTypeTag? (type : Expr) : Option String :=
  match type.getForallBody.consumeMData.getAppFn.constName? with
  | some ``Parser.Parser => some "parser"
  | some ``Parser.TrailingParser => some "trailingParser"
  | some ``Parser.ParserFn => some "parserFn"
  | some ``ParserDescr => some "descr"
  | some ``TrailingParserDescr => some "trailingDescr"
  | _ => none

def strLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- Decodes a `Name` literal as the elaborator produces it for a quoted name. -/
partial def nameLit? (e : Expr) : Option Name := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  let c ← fn.constName?
  if c == ``Name.anonymous && args.isEmpty then
    return .anonymous
  if (c == ``Name.str || c == ``Name.mkStr) && args.size == 2 then
    return .str (← nameLit? args[0]!) (← strLit? args[1]!)
  if (c == ``Name.num || c == ``Name.mkNum) && args.size == 2 then
    return .num (← nameLit? args[0]!) (← args[1]!.nat? <|> args[1]!.rawNatLit?)
  if c == ``Name.mkSimple && args.size == 1 then
    return .str .anonymous (← strLit? args[0]!)
  if c.getPrefix == ``Name then
    if let .str _ s := c then
      if s.startsWith "mkStr" && (s.drop 5).toNat? == some args.size then
        return ← args.foldlM (init := Name.anonymous) fun n a => return .str n (← strLit? a)
  none

/-- The `Name` literals in `e`, which include the syntax node kinds that a parser produces. -/
partial def nameLits (e : Expr) : NameSet :=
  (go e |>.run ({}, {})).2.2
where
  go (e : Expr) : StateM (Std.HashSet Expr × NameSet) Unit := do
    if (← get).1.contains e then
      return
    modify fun (v, ns) => (v.insert e, ns)
    if let some n := nameLit? e then
      unless n.isAnonymous do
        modify fun (v, ns) => (v, ns.insert n)
      return
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()

/-- Same as `Lean.Fmt.isAntiquotKind`, which is private. -/
def isAntiquotKind : SyntaxNodeKind → Bool
  | .str _ "antiquot"
  | .str _ "antiquot_scope"
  | .str _ "antiquot_splice"
  | .str _ "antiquot_suffix_splice"
  | .str .anonymous "token_antiquot" =>
    true
  | _ => false

/--
Generic kinds such as `ident`, `num`, `group` or `token.disch` occur in many parsers, so no parser
defines them.
-/
def isGenericKind (k : SyntaxNodeKind) : Bool :=
  k.getPrefix.isAnonymous || k.getRoot == `token

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The functions to which `panic!`, `unreachable!` and `assert!` pass the position of the call. -/
def posFns : List Name :=
  [``panicWithPos, ``panicWithPosWithDecl, ``mkPanicMessage, ``mkPanicMessageWithDecl]

/--
Removes the parts of a term that change when unrelated code changes: the source positions that
`panic!` and its relatives put into the term, and the module-wide numbers of `_auxLemma`s.
-/
def normalize (e : Expr) : Expr :=
  e.replace fun
    | .const (.num p _) us =>
      if p matches .str _ "_auxLemma" then some (.const p us) else none
    | e@(.app ..) => do
      let c ← e.getAppFn.constName?
      guard <| posFns.contains c
      let args := e.getAppArgs.map fun a =>
        if a.nat?.isSome || a.rawNatLit?.isSome then mkRawNatLit 0 else a
      return mkAppN e.getAppFn args
    | _ => none

def declHash (ci : ConstantInfo) : String :=
  let value := ci.value? (allowOpaque := true) |>.map (hash ∘ normalize) |>.getD 0
  hex <| mixHash (hash ci.type) value

def moduleOf (env : Environment) (n : Name) : Json :=
  match env.getModuleIdxFor? n with
  | some idx => toJson (env.header.moduleNames[idx.toNat]?.getD .anonymous)
  | none => .null

def linesOf (env : Environment) (n : Name) : Json :=
  let r? := declRangeExt.find? (level := .exported) env n <|>
    declRangeExt.find? (level := .server) env n
  match r? with
  | some r => toJson #[r.range.pos.line, r.range.endPos.line]
  | none => .null

/-- The declaration that an auxiliary declaration such as `f.match_1` or `f._lambda_1` belongs to. -/
partial def userDecl : Name → Name
  | n@(.str p s) =>
    if !p.isAnonymous && (s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_") then
      userDecl p
    else
      n
  | .num p _ => userDecl p
  | n => n

def nameStrs (ns : Array Name) : Json :=
  toJson (ns.map toString |>.qsort (· < ·))

def run (out : System.FilePath) : IO Unit := do
  let imports : Array Import := #[`Init, `Std, `Lean, `Lake].map ({ module := · })
  let env ← importModules (loadExts := true) imports {}
  let st := Parser.parserExtension.getState env
  let kinds : NameSet := st.kinds.foldl (init := {}) fun s k _ =>
    if isAntiquotKind k then s else s.insert k
  let aliasInfos ← Parser.parserAliases2infoRef.get
  -- Parser declarations
  let mut parserDecls : NameMap (String × ConstantInfo) := {}
  for (n, ci) in env.constants.toList do
    unless ci matches .defnInfo _ | .opaqueInfo _ do continue
    if (privateToUserName n).isInternal then continue
    if let some tag := parserTypeTag? ci.type then
      parserDecls := parserDecls.insert n (tag, ci)
  let mut declsJson : Array (String × Json) := #[]
  let mut owners : NameMap (Array Name) := {}
  for (n, tag, ci) in parserDecls do
    let value? := ci.value? (allowOpaque := true)
    let lits := value?.map nameLits |>.getD {}
    let consts := value?.map (·.getUsedConstantsAsSet) |>.getD {}
    let mut deps : NameSet := {}
    for c in consts do
      if c != n && parserDecls.contains c then
        deps := deps.insert c
    for l in lits do
      if l != n && parserDecls.contains l then
        deps := deps.insert l
      else if let some info := aliasInfos.find? l then
        if !info.declName.isAnonymous && info.declName != n then
          deps := deps.insert info.declName
    -- A kind that names a parser declaration is defined by that declaration, not by its users.
    let mut defined : Array Name := if kinds.contains n then #[n] else #[]
    for l in lits do
      if l != n && kinds.contains l && !parserDecls.contains l && !aliasInfos.contains l &&
          !isGenericKind l then
        defined := defined.push l
    for k in defined do
      owners := owners.insert k ((owners.getD k #[]).push n)
    declsJson := declsJson.push (n.toString, Json.mkObj [
      ("type", tag),
      ("module", moduleOf env n),
      ("lines", linesOf env n),
      ("hash", declHash ci),
      ("deps", nameStrs deps.toArray),
      ("kinds", nameStrs defined)
    ])
  -- Kinds and their formatters
  let providers := Fmt.getFmtProviders env
  let mut kindCats : NameMap (Array Name) := {}
  for (cat, c) in st.categories do
    for (k, _) in c.kinds do
      kindCats := kindCats.insert k ((kindCats.getD k #[]).push cat)
  -- The formatter code that mentions each kind. A quotation pattern of a formatter compiles to
  -- `Syntax.isOfKind` checks, so this finds the kinds that the formatter of a parent syntax matches.
  let mut fmtRefs : NameMap NameSet := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Lean.Fmt).isPrefixOf mod || (`Lake.Formatters).isPrefixOf mod do continue
    -- Theorems and the helpers of structures mention kinds only in types.
    if ci matches .thmInfo _ || isAuxRecursor env n || isNoConfusion env n then continue
    if n.components.any fun c =>
        c.toString.startsWith "_sizeOf" || c.toString.startsWith "noConfusion" then
      continue
    let some value := ci.value? (allowOpaque := true) | continue
    let user := userDecl (privateToUserName n)
    for l in nameLits value do
      if kinds.contains l && l != user then
        fmtRefs := fmtRefs.insert l ((fmtRefs.getD l {}).insert user)
  let mut kindsJson : Array (String × Json) := #[]
  let mut fmtDecls : NameSet := {}
  for k in kinds do
    let mut fmt := Json.null
    for p in providers do
      if let some (fmtName, _) := p.provider env {} k then
        fmt := Json.mkObj [("priority", p.priority), ("decl", fmtName.toString)]
        if p.priority == 1000 || p.priority == 800 then
          fmtDecls := fmtDecls.insert fmtName
        break
    let mut fields := [
      ("owners", nameStrs (owners.getD k #[])),
      ("categories", nameStrs (kindCats.getD k #[])),
      ("private", isPrivateName k),
      ("fmt", fmt)
    ]
    if fmt.isNull then
      fields := fields ++ [("fmtRefs", nameStrs (fmtRefs.getD k {}).toArray)]
    kindsJson := kindsJson.push (k.toString, Json.mkObj fields)
  let fmtsJson : Array (String × Json) := fmtDecls.toArray.map fun n =>
    let hash := match env.find? n with
      | some ci => toJson (declHash ci)
      | none => .null
    (n.toString, Json.mkObj [
      ("module", moduleOf env n),
      ("lines", linesOf env n),
      ("hash", hash)
    ])
  let catsJson : Array (String × Json) := st.categories.toList.toArray.map fun (cat, c) =>
    let behavior := match c.behavior with
      | .default => "default"
      | .symbol => "symbol"
      | .both => "both"
    (cat.toString, Json.mkObj [
      ("decl", c.declName.toString),
      ("module", moduleOf env c.declName),
      ("lines", linesOf env c.declName),
      ("behavior", behavior)
    ])
  let tokens := st.tokens.values.qsort (· < ·)
  let obj := fun (xs : Array (String × Json)) =>
    Json.mkObj (xs.qsort (·.1 < ·.1)).toList
  let json := Json.mkObj [
    ("version", 1),
    ("decls", obj declsJson),
    ("kinds", obj kindsJson),
    ("fmts", obj fmtsJson),
    ("categories", obj catsJson),
    ("tokens", toJson tokens)
  ]
  IO.FS.writeFile out json.compress

end FmtReview

def main (args : List String) : IO UInt32 := do
  let [out] := args
    | IO.eprintln "usage: lean --run inventory.lean <out.json>"
      return 2
  unsafe enableInitializersExecution
  FmtReview.run out
  return 0
