/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.Server.Snapshots
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

namespace Lean
namespace Server

/-
Each file worker process manages a single file. File workers are launched and terminated
by a watchdog process. See Watchdog.lean for a description of how file workers are expected 
to interact with the watchdog process.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.
-/

open Lsp
open IO
open Snapshots

private def sendDiagnosticsCore (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) (log : MessageLog)
  : IO Unit :=
let diagnostics := log.msgs.map (msgToDiagnostic text);
Lsp.writeLspNotification h "textDocument/publishDiagnostics"
  { uri := uri,
    version? := version,
    diagnostics := diagnostics.toArray : PublishDiagnosticsParams }

inductive AbortedOrEOF
| Aborted
| EOF

inductive ElabTask
| mk (data : Snapshot) (next : Task (IO (Except AbortedOrEOF ElabTask))) : ElabTask

namespace ElabTask

private def runCore (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap) (parent : Snapshot) : IO (Except AbortedOrEOF ElabTask) := do
result ← compileNextCmd contents.source parent;
-- TODO(MH): check for interrupt
sendDiagnosticsCore h uri
pure $ match result with
| Sum.inl snap => Except.ok ⟨snap, Task.mk (fun _ => runCore h uri version contents snap)⟩  
| Sum.inr msgLog => Except.error AbortedOrEOF.EOF

def run (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap) (parent : Snapshot) : ElabTask :=
⟨parent, Task.mk (fun _ => runCore h uri version contents parent)⟩

-- TODO(MH)
def nextHasFinished (t : ElabTask) : IO Bool :=
pure true

def interruptNext (t : ElabTask) : IO Unit :=
pure ()

end ElabTask

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument :=
(version : Nat)
(text : FileMap)
/- The first snapshot is that after the header. -/
-- (header : Snapshot)
/- Subsequent snapshots occur after each command. -/
-- TODO(WN): These should probably be asynchronous Tasks
(snapshots : ElabTask)

namespace EditableDocument

open Elab

/-- Compiles the contents of a Lean file. -/
def compileDocument (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) : IO EditableDocument := do
headerSnap ← Snapshots.compileHeader text.source;
let task := ElabTask.run h uri version text headerSnap;
let docOut : EditableDocument := ⟨version, text, task⟩;
pure docOut

/-- Given `changePos`, the UTF-8 offset of a change into the pre-change source,
and the new document, updates editable doc state. -/
def updateDocument (doc : EditableDocument) (changePos : String.Pos) (newVersion : Nat)
  (newText : FileMap) : IO (MessageLog × EditableDocument) := do
let recompileEverything := (do
  -- TODO free compacted regions
  compileDocument newVersion newText);
/- If the change occurred before the first command
or there are no commands yet, recompile everything. -/
match doc.snapshots.head? with
| none => recompileEverything
| some firstSnap =>
  if firstSnap.beginPos > changePos then
    recompileEverything
  else do
    -- NOTE(WN): endPos is greedy in that it consumes input until the next token,
    -- so a change on some whitespace after a command recompiles it. We could
    -- be more precise.
    let validSnaps := doc.snapshots.filter (fun snap => snap.endPos < changePos);
    -- The lowest-in-the-file snapshot which is still valid.
    let lastSnap := validSnaps.getLastD doc.header;
    (snaps, msgLog) ← Snapshots.compileCmdsAfter newText.source lastSnap;
    let newDoc := { version := newVersion,
                    header := doc.header,
                    text := newText,
                    snapshots := validSnaps ++ snaps : EditableDocument };
    pure (msgLog, newDoc)

end EditableDocument

open EditableDocument

open IO
open Std (RBMap RBMap.empty)
open JsonRpc

structure ServerContext :=
(hIn hOut : FS.Stream)
(docRef : IO.Ref EditableDocument)
-- TODO (requestsInFlight : IO.Ref (Array (Task (Σ α, Response α))))

abbrev ServerM := ReaderT ServerContext IO

def setDocument (val : EditableDocument) : ServerM Unit :=
fun st => st.docRef.set val

def getDocument : ServerM EditableDocument :=
fun st => st.docRef.get

def readLspMessage : ServerM JsonRpc.Message :=
fun st => monadLift $ readLspMessage st.hIn

def readLspRequestAs (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM (Request α) :=
fun st => monadLift $ readLspRequestAs st.hIn expectedMethod α

def readLspNotificationAs (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM α :=
fun st => monadLift $ readLspNotificationAs st.hIn expectedMethod α

def writeLspNotification {α : Type*} [HasToJson α] (method : String) (params : α) : ServerM Unit :=
fun st => monadLift $ writeLspNotification st.hOut method params

def writeLspResponse {α : Type*} [HasToJson α] (id : RequestID) (params : α) : ServerM Unit :=
fun st => monadLift $ writeLspResponse st.hOut id params

/-- Clears diagnostics for the document version 'version'. -/
-- TODO(WN): how to clear all diagnostics? Sending version 'none' doesn't seem to work
def clearDiagnostics (uri : DocumentUri) (version : Nat) : ServerM Unit :=
writeLspNotification "textDocument/publishDiagnostics"
  { uri := uri,
    version? := version,
    diagnostics := #[] : PublishDiagnosticsParams }

def sendDiagnostics (uri : DocumentUri) (doc : EditableDocument) (log : MessageLog)
  : ServerM Unit := do
fun st => monadLift $ sendDiagnosticsCore st.hOut uri doc log

def openDocument (h : FS.Stream) (p : DidOpenTextDocumentParams) : IO EditableDocument := do
let doc := p.textDocument;
-- NOTE(WN): `toFileMap` marks line beginnings as immediately following
-- "\n", which should be enough to handle both LF and CRLF correctly.
-- This is because LSP always refers to characters by (line, column),
-- so if we get the line number correct it shouldn't matter that there
-- is a CR there.
let text := doc.text.toFileMap;
(msgLog, newDoc) ← compileDocument doc.version text;
sendDiagnosticsCore h doc.uri newDoc msgLog;
pure newDoc

private def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
let start := text.lspPosToUtf8Pos r.start;
let «end» := text.lspPosToUtf8Pos r.«end»;
let pre := text.source.extract 0 start;
let post := text.source.extract «end» text.source.bsize;
(pre ++ newText ++ post).toFileMap

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
let docId := p.textDocument;
let changes := p.contentChanges;
oldDoc ← getDocument;
some newVersion ← pure docId.version? | throw (userError "expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "got outdated version number")
else changes.forM $ fun change =>
  match change with
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) => do
    let startOff := oldDoc.text.lspPosToUtf8Pos range.start;
    let newDocText := replaceLspRange oldDoc.text range newText;
    (msgLog, newDoc) ← monadLift $
      updateDocument oldDoc startOff newVersion newDocText;
    setDocument newDoc;
    -- Clients don't have to clear diagnostics, so we clear them
    -- for the *previous* version here.
    clearDiagnostics docId.uri oldDoc.version;
    sendDiagnostics docId.uri newDoc msgLog
  | TextDocumentContentChangeEvent.fullChange (text : String) =>
    throw (userError "TODO impl computing the diff of two sources.")

def handleHover (p : HoverParams) : ServerM Json := pure Json.null

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let h := (fun paramType [HasFromJson paramType] (handler : paramType → ServerM Unit) =>
  parseParams paramType params >>= handler);
match method with
| "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
| "$/cancelRequest"        => pure () -- TODO when we're async
| _                        => throw (userError "got unsupported notification method")

def handleRequest (id : RequestID) (method : String) (params : Json)
  : ServerM Unit := do
let h := (fun paramType responseType [HasFromJson paramType] [HasToJson responseType]
              (handler : paramType → ServerM responseType) =>
           parseParams paramType params >>= handler >>= writeLspResponse id);
match method with
| "textDocument/hover" => h HoverParams Json handleHover
| _ => throw (userError $ "got unsupported request: " ++ method ++
                          "; params: " ++ toString params)

partial def mainLoop : Unit → ServerM Unit
| () => do
  -- TODO(MH): gracefully terminate when stdin is closed by watchdog?
  msg ← readLspMessage;
  match msg with
  | Message.request id method (some params) => do
    handleRequest id method (toJson params);
    mainLoop ()
  | Message.notification method (some params) => do
    handleNotification method (toJson params);
    mainLoop ()
  | _ => throw (userError "got invalid JSON-RPC message")

def initAndRunServer (i o : FS.Stream) : IO Unit := do
-- ignore InitializeParams for MWE
initRequest ← Lsp.readLspRequestAs i "initialize" InitializeParams;
docRequest ← Lsp.readLspRequestAs i "textDocument/didOpen" DidOpenTextDocumentParams;
doc ← openDocument o docRequest.param;
docRef ← IO.mkRef doc;
runReader (mainLoop ()) (⟨i, o, docRef⟩ : ServerContext)

end Server
end Lean
