/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Data.Json.Basic
public import Std.Data.HashSet.Basic

public section

namespace Lean.Data.Json

abbrev StringCache := Std.HashSet String
abbrev InternM := StateM StringCache

def intern : Json → InternM Json
  | .null => pure <| .null
