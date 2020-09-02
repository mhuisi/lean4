/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.JsonRpc
import Lean.Data.Lsp.TextSync

/-! Minimal LSP servers/clients do not have to implement a lot
of functionality. Most useful additional behaviour is instead
opted into via capabilities. -/

namespace Lean
namespace Lsp

open Json

-- TODO: right now we ignore the client's capabilities
inductive ClientCapabilities | mk

instance ClientCapabilities.hasFromJson : HasFromJson ClientCapabilities :=
⟨fun j => ClientCapabilities.mk⟩

instance ClientCapabilities.hasToJson : HasToJson ClientCapabilities :=
⟨fun o => mkObj []⟩

-- TODO largely unimplemented
structure ServerCapabilities :=
(textDocumentSync? : Option TextDocumentSyncOptions := none)
(hoverProvider : Bool := false)

instance ServerCapabilities.hasToJson : HasToJson ServerCapabilities :=
⟨fun o => mkObj $
  opt "textDocumentSync" o.textDocumentSync? ++
  [⟨"hoverProvider", o.hoverProvider⟩]⟩

end Lsp
end Lean
