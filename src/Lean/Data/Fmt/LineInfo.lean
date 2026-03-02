/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Error
import Init.While
import Init.Data.Slice

namespace Lean.Fmt

public structure LineInfo (s : String.Slice) where
  length : Nat
  indentation : Nat
  range : s.Subslice
  deriving Inhabited

/--
For every line in `s`, determines the length of the line in characters, the level of indentation
and the range of the line (without the terminal `\n`).
-/
public def collectLineInfos (s : String.Slice) : Array (LineInfo s) := Id.run do
  let mut r := #[]
  let mut lineLength : Nat := 0
  let mut lineIndentation : Nat := 0
  let mut foundNonSpaceChar : Bool := false
  let mut lineStartPos := s.startPos
  let mut pos := s.startPos
  while h : pos ≠ s.endPos do
    let c := pos.get h
    let pos' := pos.next h
    if c == ' ' && ! foundNonSpaceChar then
      lineLength := lineLength + 1
      lineIndentation := lineIndentation + 1
    else if c == '\n' then
      r := r.push {
        length := lineLength
        indentation := lineIndentation
        range := s.subslice! lineStartPos pos
      }
      lineLength := 0
      lineIndentation := 0
      lineStartPos := pos'
      foundNonSpaceChar := false
    else
      lineLength := lineLength + 1
      foundNonSpaceChar := true
    pos := pos'
  r := r.push {
    length := lineLength
    indentation := lineIndentation
    range := s.subslice! lineStartPos pos
  }
  return r

public structure SyntaxLineInfo where
  length : Nat
  indentation : Nat
  line : String
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited

structure collectSyntaxLineInfos.State where
  finishedLines : Array SyntaxLineInfo
  pendingLine : SyntaxLineInfo

/--
For every line in `s`, determines the length of the line in characters, the level of indentation
and the range of the line (without the terminal `\n`).
-/
public partial def collectSyntaxLineInfos (stx : Syntax) : Array SyntaxLineInfo :=
  let (_, s) := StateT.run (go stx) {
    finishedLines := #[]
    pendingLine := { length := 0, indentation := 0, line := "", startPos := ⟨0⟩, endPos := ⟨0⟩ }
  }
  s.finishedLines.push s.pendingLine

where

  go (stx : Syntax) : StateM collectSyntaxLineInfos.State Unit := do
    match stx with
    | .missing =>
      return
    | .atom info val =>
      advanceBy val
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing
    | .ident info rawVal .. =>
      advanceBy rawVal.toString
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing
    | .node _ _ args =>
      for arg in args do
        go arg

  advanceBy (s : String) :
      StateM collectSyntaxLineInfos.State Unit := do
    let lineInfos := collectLineInfos s
    let pendingLine := (← get).pendingLine
    let pendingLine' := lineInfos[0]!
    let mut startPos := pendingLine.startPos
    let endPos := pendingLine.endPos.increaseBy pendingLine'.range.toSlice.utf8ByteSize
    let combinedPendingLine : SyntaxLineInfo := {
      length := pendingLine.length + pendingLine'.length
      indentation :=
        if pendingLine.indentation < pendingLine.length then
          pendingLine.indentation
        else
          pendingLine.indentation + pendingLine'.indentation
      line := pendingLine.line ++ pendingLine'.range.toString
      startPos
      endPos
    }
    let mut newLineInfos := #[combinedPendingLine]
    startPos := endPos + '\n'
    for lineInfo in lineInfos[1...*] do
      let endPos := startPos.increaseBy lineInfo.range.toSlice.utf8ByteSize
      newLineInfos := newLineInfos.push {
        length := lineInfo.length
        indentation := lineInfo.indentation
        line := lineInfo.range.toString
        startPos
        endPos
      }
      startPos := endPos + '\n'
    let pendingLine := newLineInfos.back!
    let finishedLines := newLineInfos.pop
    modify fun s => { s with
      finishedLines := s.finishedLines ++ finishedLines
      pendingLine
    }
