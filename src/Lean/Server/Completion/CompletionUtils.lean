/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Init.Prelude

namespace Lean.Server.Completion

inductive HoverInfo : Type where
  | after
  | inside (delta : Nat)

end Lean.Server.Completion
