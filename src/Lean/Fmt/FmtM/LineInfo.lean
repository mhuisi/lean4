/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Error
import Init.While
import Init.Data.Slice
import Lean.Fmt.Util.Basic
public import Lean.Syntax

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

/-- The part of a token that lies on a single line. -/
public structure SyntaxLineToken where
  /-- Start of the token, or `none` if the token started in a previous line. -/
  startPos : String.Pos.Raw
  /-- End of the token, or `none` if the token ends in one of the next lines. -/
  endPos : String.Pos.Raw

public structure SyntaxLineInfo where
  length : Nat
  indentation : Nat
  line : String
  /-- The parts of the tokens that lie on this line, ordered by position. -/
  tokenRanges : Array Syntax.Range
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited

public instance : ToString SyntaxLineInfo where
  toString li := s!"{li.line} [{li.startPos} - {li.endPos}; #{li.length}; i{li.indentation}]"

structure collectSyntaxLineInfos.State where
  finishedLines : Array SyntaxLineInfo
  pendingLine : SyntaxLineInfo

/--
For every line in `s`, determines the length of the line in characters, the level of indentation,
the range of the line (without the terminal `\n`) and the parts of the tokens of `stx` that lie on
the line.
-/
public partial def collectSyntaxLineInfos (stx : Syntax) : Array SyntaxLineInfo :=
  let startPos := stx.getStartPos?.getD ⟨0⟩
  let (_, s) := StateT.run (go stx) {
    finishedLines := #[]
    pendingLine := {
      length := 0
      indentation := 0
      line := ""
      tokenRanges := #[]
      startPos
      endPos := startPos
    }
  }
  s.finishedLines.push s.pendingLine

where

  go (stx : Syntax) : StateM collectSyntaxLineInfos.State Unit := do
    match stx with
    | .missing =>
      return
    | .atom info val =>
      if let some leading := info.getLeading?.map (·.toString) then
        advanceBy leading (isToken := false)
      advanceBy val (isToken := true)
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing (isToken := false)
    | .ident info rawVal .. =>
      if let some leading := info.getLeading?.map (·.toString) then
        advanceBy leading (isToken := false)
      advanceBy rawVal.toString (isToken := true)
      if let some trailing := info.getTrailing?.map (·.toString) then
        advanceBy trailing (isToken := false)
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg

  advanceBy (s : String) (isToken : Bool) :
      StateM collectSyntaxLineInfos.State Unit := do
    let lineInfos := collectLineInfos s
    let pendingLine := (← get).pendingLine
    -- `s` is appended at the current position, which is the end of the pending line.
    let tokenStartPos := pendingLine.endPos
    let tokenEndPos := tokenStartPos.increaseBy s.utf8ByteSize
    let lineTokenRanges : Array Syntax.Range := Id.run do
      if ! isToken then
        return #[]
      let token := ⟨tokenStartPos, tokenEndPos⟩
      return #[token]
    let pendingLine' := lineInfos[0]!
    let mut startPos := pendingLine.startPos
    let endPos := pendingLine.endPos.increaseBy pendingLine'.range.toSlice.utf8ByteSize
    let combinedPendingLine : SyntaxLineInfo := {
      length := pendingLine.length + pendingLine'.length
      indentation :=
        if pendingLine.indentation < pendingLine.length || isToken then
          pendingLine.indentation
        else
          pendingLine.indentation + pendingLine'.indentation
      line := pendingLine.line ++ pendingLine'.range.toString
      tokenRanges := pendingLine.tokenRanges ++ lineTokenRanges
      startPos
      endPos
    }
    let mut newLineInfos := #[combinedPendingLine]
    startPos := endPos + '\n'
    for lineInfo in lineInfos[1...*] do
      let endPos := startPos.increaseBy lineInfo.range.toSlice.utf8ByteSize
      newLineInfos := newLineInfos.push {
        length := lineInfo.length
        indentation :=
          if ! isToken then
            lineInfo.indentation
          else
            0
        line := lineInfo.range.toString
        tokenRanges := lineTokenRanges
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

-- TODO: Delete once Verso docstrings are fixed.
section ImplementationForBrokenVerso

/--
A range of `stx` in which lines starting within the range are considered to start in a token.
-/
structure collectSyntaxLineInfos'.TokenRange where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  /--
  Whether this range covers tokens without source positions.
  Lines starting anywhere in such a range are assumed to start in a token,
  including lines starting exactly at `startPos`.
  By contrast, a line starting exactly at the `startPos` of a token with source positions is not
  considered to start in the token.
  -/
  isBrokenRegion : Bool
  deriving Inhabited

structure collectSyntaxLineInfos'.State where
  /-- Sorted by `startPos` and disjoint, provided that the tokens in `stx` are. -/
  tokenRanges : Array collectSyntaxLineInfos'.TokenRange := #[]
  /--
  End position of the trailing whitespace of the last token with source positions,
  or the start of the source if no such token has been encountered yet.
  -/
  lastPositionedTokenTrailingStopPos : String.Pos.Raw
  /--
  Whether a token without source positions has been encountered since the last token with source
  positions.
  -/
  hasPendingBrokenRegion : Bool := false

/--
For every line in `source`, determines the length of the line in characters, the level of
indentation and the range of the line (without the terminal `\n`),
as well as whether the line starts within a token of `stx` and which parts of the tokens of `stx`
lie on the line.

`source` must be the slice of the source text that is covered by `stx`,
including the leading whitespace of its first token and the trailing whitespace of its last token.

In contrast to `collectSyntaxLineInfos`, this function computes all line information directly from
`source` and only uses `stx` to determine which lines start within a token.
Hence, it also produces accurate line information when `stx` contains tokens without source
positions, as is currently the case for Verso docstrings.
All lines starting between the tokens with source positions that surround such broken tokens are
conservatively assumed to start in a token, and the whole region between those tokens is
conservatively reported as a single token.
-/
public partial def collectSyntaxLineInfos' (source : String.Slice) (stx : Syntax) :
    Array SyntaxLineInfo := Id.run do
  let sourceStartPos := source.startInclusive.offset
  let (_, s) := StateT.run (go stx) {
    lastPositionedTokenTrailingStopPos := sourceStartPos
  }
  let mut tokenRanges := s.tokenRanges
  if s.hasPendingBrokenRegion then
    tokenRanges := tokenRanges.push {
      startPos := s.lastPositionedTokenTrailingStopPos
      endPos := source.endExclusive.offset
      isBrokenRegion := true
    }
  let mut syntaxLineInfos := #[]
  let mut tokenRangeIdx := 0
  for lineInfo in collectLineInfos source do
    let lineStartPos := lineInfo.range.startInclusive.offset.offsetBy sourceStartPos
    let lineEndPos := lineInfo.range.endExclusive.offset.offsetBy sourceStartPos
    while tokenRangeIdx < tokenRanges.size
        && tokenRanges[tokenRangeIdx]!.endPos <= lineStartPos do
      tokenRangeIdx := tokenRangeIdx + 1
    let startsInToken := lineStartsInTokenRange lineStartPos tokenRanges[tokenRangeIdx]?
    -- Token ranges spanning several lines are visited once per line they cover,
    -- so `tokenRangeIdx` must not be advanced here.
    let mut lineTokenRanges := #[]
    let mut idx := tokenRangeIdx
    while idx < tokenRanges.size && tokenRanges[idx]!.startPos < lineEndPos do
      let tokenRange := tokenRanges[idx]!
      let tokenRange := ⟨tokenRange.startPos, tokenRange.endPos⟩
      lineTokenRanges := lineTokenRanges.push tokenRange
      idx := idx + 1
    syntaxLineInfos := syntaxLineInfos.push {
      length := lineInfo.length
      indentation := if startsInToken then 0 else lineInfo.indentation
      line := lineInfo.range.toString
      tokenRanges := lineTokenRanges
      startPos := lineStartPos
      endPos := lineEndPos
    }
  return syntaxLineInfos

where

  go (stx : Syntax) : StateM collectSyntaxLineInfos'.State Unit := do
    match stx with
    | .missing =>
      return
    | .atom info _ =>
      visitToken info
    | .ident info .. =>
      visitToken info
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg

  visitToken (info : SourceInfo) : StateM collectSyntaxLineInfos'.State Unit := do
    let (some pos, some tailPos) := (info.getPos?, info.getTailPos?)
      | modify fun s => { s with hasPendingBrokenRegion := true }
    if (← get).hasPendingBrokenRegion then
      modify fun s => { s with
        tokenRanges := s.tokenRanges.push {
          startPos := s.lastPositionedTokenTrailingStopPos
          endPos := info.getLeading?.map (·.startPos) |>.getD pos
          isBrokenRegion := true
        }
        hasPendingBrokenRegion := false
      }
    modify fun s => { s with
      tokenRanges := s.tokenRanges.push {
        startPos := pos
        endPos := tailPos
        isBrokenRegion := false
      }
      lastPositionedTokenTrailingStopPos := info.getTrailing?.map (·.stopPos) |>.getD tailPos
    }

  lineStartsInTokenRange
      (lineStartPos : String.Pos.Raw)
      (tokenRange? : Option collectSyntaxLineInfos'.TokenRange) :
      Bool :=
    match tokenRange? with
    | none =>
      false
    | some tokenRange =>
      lineStartPos < tokenRange.endPos
        && (tokenRange.startPos < lineStartPos
          || (tokenRange.isBrokenRegion && tokenRange.startPos == lineStartPos))

end ImplementationForBrokenVerso
