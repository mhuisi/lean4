import Init.System.IO

import Lean.Server.Snapshots

namespace Lean
namespace Server

open Snapshots

inductive AbortedOrEOF
| Aborted
| EOF

inductive ElabTask
| mk (data : Snapshot) (next : Task (IO (Except AbortedOrEOF ElabTask))) : ElabTask

namespace ElabTask

private def runCore (contents : String) (parent : Snapshot) : IO (Except AbortedOrEOF ElabTask) := do
result ← compileNextCmd contents parent;
-- TODO(MH): check for interrupt
pure $ match result with
| Sum.inl snap => Except.ok ⟨snap, Task.mk (fun _ => runCore contents snap)⟩  
| Sum.inr msgLog => Except.error AbortedOrEOF.EOF

def run (contents : String) (parent : Snapshot) : ElabTask :=
⟨parent, Task.mk (fun _ => runCore contents parent)⟩

-- TODO(MH)
def nextHasFinished (t : ElabTask) : IO Bool :=
pure true

def interruptNext (t : ElabTask) : IO Unit :=
pure ()

end ElabTask

end Server
end Lean
