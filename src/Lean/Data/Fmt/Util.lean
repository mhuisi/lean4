/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Ord.Basic
public import Init.Data.String.Subslice
import Init.Data.Hashable
import Init.Data.ToString

deriving instance Hashable, Ord for String.Pos.Raw
deriving instance Hashable, Ord for String.Slice.Pos
deriving instance BEq, Hashable for String.Slice.Subslice

public instance : ToString (String.Slice.Subslice s) where
  toString s := s!"{s.startInclusive.offset} - {s.endExclusive.offset}"

public instance : Repr (String.Slice.Subslice s) where
  reprPrec s _ := toString s
