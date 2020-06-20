prelude
import Init.System.IO
import Init.Lean.Data.Json.Parser
import Init.Lean.Data.Json.Printer
import Init.Lean.Data.Json.FromToJson

namespace IO.FS.Handle

open Lean
open IO

def readJson (h : FS.Handle) (nBytes : Nat) : IO Json := do
bytes ← h.read nBytes;
j ← ofExcept (Json.parse (toString bytes));
pure j

def writeJson (h : FS.Handle) (j : Json) : IO Unit :=
h.putStr j.compress

end IO.FS.Handle
