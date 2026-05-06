/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.Tactics
meta import Std.Tactic.BVDecide.Syntax
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.Tactic.bvCheck]
public def fmtBvCheck : Fmt := fun
  | `(tactic| bv_check%$bvCheckTk $cfg:optConfig $lratFile:str) => do
    let bvCheckTk ← fmt bvCheckTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    let lratFile ← fmt lratFile
    return Layouts.pseudoApplication <| #[bvCheckTk] ++ cfg ++ #[lratFile]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvDecide]
public def fmtStdBvDecide : Fmt := fun
  | `(tactic| bv_decide%$bvDecideTk $cfg:optConfig) => do
    let bvDecideTk ← fmt bvDecideTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[bvDecideTk] ++ cfg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvTrace]
public def fmtStdBvTrace : Fmt := fun
  | `(tactic| bv_decide?%$bvTraceTk $cfg:optConfig) => do
    let bvTraceTk ← fmt bvTraceTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[bvTraceTk] ++ cfg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Tactic.bvNormalize]
public def fmtStdBvNormalize : Fmt := fun
  | `(tactic| bv_normalize%$bvNormalizeTk $cfg:optConfig) => do
    let bvNormalizeTk ← fmt bvNormalizeTk
    let cfg ← (← tacticOptConfigItems cfg).mapM fmt
    return Layouts.pseudoApplication <| #[bvNormalizeTk] ++ cfg
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.bv_normalize]
public def fmtBvNormalizeAttr : Fmt := fun
  | `(Parser.bv_normalize| bv_normalize%$bvNormalizeTk $[$dir?]? $[←%$revTk?]? $[$prio?:prio]?) =>
    fmtSimpAttrLike bvNormalizeTk dir? revTk? prio?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.bvNormalizeProcBuiltinAttr]
public def fmtBvNormalizeProcBuiltinAttr : Fmt := fun
  | `(Parser.bvNormalizeProcBuiltinAttr| builtin_bv_normalize_proc%$builtinTk $[$dir?]?) =>
    fmtSimpAttrLike builtinTk dir? none none
  | _ => throw .partialFormatter
