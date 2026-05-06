/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term
public import Lean.Fmt.Formatters.Std.Do.Triple.Basic
meta import Std.Internal.Do.Triple.Basic
import Init.Data

namespace Lean.Fmt

open Std.Internal.Do in
@[builtin_fmt Std.Internal.Do.tripleNotation]
public def fmtTripleNotation : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $post ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let post ← fmt post
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk ⟨#[post]⟩ postRbTk
  | _ => throw .partialFormatter

open Std.Internal.Do in
@[builtin_fmt Std.Internal.Do.tripleBinderNotation]
public def fmtTripleBinderNotation : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $binder:ident ,%$commaTk $post ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let binder ← fmt binder
    let commaTk ← fmt commaTk
    let post ← fmt post
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk ⟨#[binder, commaTk, post]⟩
      postRbTk
  | _ => throw .partialFormatter

open Std.Internal.Do in
@[builtin_fmt Std.Internal.Do.tripleEPost]
public def fmtTripleEPost : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $post ;%$semicolonTk $epost ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let post ← fmt post
    let semicolonTk ← fmt semicolonTk
    let epost ← fmt epost
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk ⟨#[post, semicolonTk, epost]⟩
      postRbTk
  | _ => throw .partialFormatter

open Std.Internal.Do in
@[builtin_fmt Std.Internal.Do.tripleBinderEPost]
public def fmtTripleBinderEPost : Fmt := fun
  | `(⦃%$preLbTk $pre ⦄%$preRbTk $[(%$mLbTk? $m?:ident :=%$mColonEqTk? $mVal? )%$mRbTk?]? $prog
      ⦃%$postLbTk $binder:ident ,%$commaTk $post ;%$semicolonTk $epost ⦄%$postRbTk) => do
    let preLbTk ← fmt preLbTk
    let pre ← fmt pre
    let preRbTk ← fmt preRbTk
    let namedArg ← fmtNamedArgumentTerm? mLbTk? m? mColonEqTk? mVal? mRbTk?
    let prog ← fmt prog
    let postLbTk ← fmt postLbTk
    let binder ← fmt binder
    let commaTk ← fmt commaTk
    let post ← fmt post
    let semicolonTk ← fmt semicolonTk
    let epost ← fmt epost
    let postRbTk ← fmt postRbTk
    return hoareTriple preLbTk pre preRbTk namedArg prog postLbTk
      ⟨#[binder, commaTk, post, semicolonTk, epost]⟩ postRbTk
  | _ => throw .partialFormatter
