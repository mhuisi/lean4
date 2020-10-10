import Lean.Data.Position
import Lean.Data.Lsp

namespace IO
namespace FS
namespace Stream

/-- Chains two streams by creating a new stream s.t. writing to it
just writes to `a` but reading from it also duplicates the read output
into `b`, c.f. `a | tee b` on Unix.
NB: if `a` is written to but this stream is never read from,
the output will *not* be duplicated. Use this if you only care
about the data that was actually read. -/
def chainRight (a : Stream) (b : Stream) : Stream :=
{ isEof := a.isEof,
  read := fun sz => do
    bs ← a.read sz;
    b.write bs;
    pure bs,
  getLine := do
    ln ← a.getLine;
    b.putStr ln;
    pure ln,
  flush := a.flush *> b.flush,
  write := a.write,
  putStr := a.putStr }

/-- Like `tee a | b` on Unix. See `chainOut`. -/
def chainLeft (a : Stream) (b : Stream) : Stream :=
{ isEof := b.isEof,
  read := b.read,
  getLine := b.getLine,
  flush := a.flush *> b.flush,
  write := fun bs => do
    a.write bs;
    b.write bs,
  putStr := fun s => do
    a.putStr s;
    b.putStr s }

end Stream
end FS
end IO

namespace Lean
namespace Server

def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
let start := text.lspPosToUtf8Pos r.start;
let «end» := text.lspPosToUtf8Pos r.«end»;
let pre := text.source.extract 0 start;
let post := text.source.extract «end» text.source.bsize;
(pre ++ newText ++ post).toFileMap

open IO

/-- Duplicates an I/O stream to a log file `fName` in LEAN_SERVER_LOG_DIR
if that envvar is set. -/
def maybeTee (fName : String) (isOut : Bool) (h : FS.Stream) : IO FS.Stream := do
logDir ← getEnv "LEAN_SERVER_LOG_DIR";
match logDir with
| none => pure h
| some logDir => do
  hTee ← FS.Handle.mk (System.mkFilePath [logDir, fName]) FS.Mode.write true;
  let hTee := FS.Stream.ofHandle hTee;
    pure $ if isOut then
    hTee.chainLeft h
  else
    h.chainRight hTee

open Lsp

/-- Returns the document contents with all changes applied, together with the position of the change
which lands earliest in the file. Panics if there are no changes. -/
def foldDocumentChanges (changes : @& Array Lsp.TextDocumentContentChangeEvent) (oldText : FileMap)
  : FileMap × String.Pos :=
if changes.isEmpty then panic! "Lean.Server.foldDocumentChanges: empty change array" else
let accumulateChanges : TextDocumentContentChangeEvent → FileMap × String.Pos → FileMap × String.Pos :=
  fun change ⟨newDocText, minStartOff⟩ =>
    match change with
    | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
      let startOff    := oldText.lspPosToUtf8Pos range.start;
      let newDocText  := replaceLspRange newDocText range newText;
      let minStartOff := minStartOff.min startOff;
      ⟨newDocText, minStartOff⟩
    | TextDocumentContentChangeEvent.fullChange (newText : String) =>
      ⟨newText.toFileMap, 0⟩;
-- NOTE: We assume Lean files are below 16 EiB.
changes.foldr accumulateChanges (oldText, 0xffffffff)

end Server
end Lean
