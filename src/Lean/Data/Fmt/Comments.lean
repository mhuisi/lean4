/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Syntax
public import Lean.Data.Fmt.Error
import Init
import Std.Data.HashMap.Basic
import Lean.Data.Fmt.RangeTree
public import Lean.Data.Fmt.Util
import Std.Data.HashSet.Iterator

/-- Indents all lines in `s` by `numSpaces` spaces. -/
def String.indent (s : String) (numSpaces : Nat) : String :=
  s.split "\n"
    |>.map (fun line => "".pushn ' ' numSpaces ++ line.toString)
    |>.toList
    |> "\n".intercalate

namespace Lean.Fmt

/-- Comment placement in the input `Syntax`. -/
public inductive Comment.Placement where
  | afterToken
  | onLineBeforeToken
  deriving Inhabited, Repr

/-- Kind of comment in the input `Syntax`. -/
public inductive Comment.Kind where
  | lineComment
  | blockComment
  deriving Inhabited, Repr

/-- Symbol that the comment starts with. -/
def Comment.Kind.startSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "--"
  | .blockComment => "/-"

/-- Symbol that the comment is terminated with. -/
def Comment.Kind.endSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "\n"
  | .blockComment => "-/"

/-- Whether this kind of comment can be nested, e.g. `/-/-foo-/-/`. -/
def Comment.Kind.hasNesting (kind : Comment.Kind) : Bool :=
  match kind with
  | .lineComment => false
  | .blockComment => true

/-- Prefix that lines after the first line of the comment are prefixed with. -/
def Comment.Kind.linePrefix? (kind : Comment.Kind) : Option String :=
  match kind with
  | .lineComment => some "--"
  | .blockComment => none

/-- Where this comment should be placed in the rendered document. -/
inductive Comment.RenderedPlacement where
  | afterClosestPreviousNewline
  | beforeClosestNextNewline
  | afterToken

/-- Comment extracted from an input `Syntax`. -/
public structure Comment where
  kind : Comment.Kind
  placement : Comment.Placement
  /--
  Content of the comment separated into lines.
  Excludes the comment separators and all whitespace within the comment that serves as indentation
  of the comment relative to the start symbol of the comment.
  -/
  content : Array String
  deriving Inhabited, Repr

/-- Renders this comment to a string. -/
def Comment.toString (c : Comment) : String :=
  match c.kind with
  | .lineComment =>
    c.content.map (s!"-- {·}") |>.toList |> "\n".intercalate
  | .blockComment =>
    if c.content.size == 1 then
      s!"/- {c.content[0]!} -/"
    else
      s!"/-\n{"\n".intercalate c.content.toList}\n-/"

/--
Yields a set of alternative placements of this comment in a rendered output, sorted descendingly
by priority.
If a specific placement does not fit into the line it is placed at, a lower priority placement
is preferred.
Ensures that the lowest priority placement always fits into a line.
-/
def Comment.renderedPlacements (c : Comment) : Array RenderedPlacement :=
  let isMultiLine := c.content.size > 1
  match c.kind, c.placement with
  | .lineComment, .afterToken =>
    if isMultiLine then
      #[.afterClosestPreviousNewline]
    else
      #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
  | .lineComment, .onLineBeforeToken =>
    #[.afterClosestPreviousNewline]
  | .blockComment, .afterToken =>
    if isMultiLine then
      #[.afterClosestPreviousNewline]
    else
      #[.afterToken, .afterClosestPreviousNewline]
  | .blockComment, .onLineBeforeToken =>
    #[.afterClosestPreviousNewline]

section Extraction

structure PendingComment extends Comment where
  full : String
  startColumnOffset : Nat
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited

def PendingComment.finalize (p : PendingComment) : Comment :=
  let s := p.full.toSlice.dropPrefix p.kind.startSymbol
    |>.dropSuffix p.kind.endSymbol
  let lines := s.split "\n" |>.toArray
  let deindentedLines :=
    lines[0]! ::
      (lines[1:].toList.map (dropIndentation · p.startColumnOffset) |>.map dropLinePrefix)
  let deindentedLines := deindentedLines.map (·.toString)
  let content := "\n".intercalate deindentedLines
    |>.toSlice
    |> normalizeContent p.kind
    |>.toString
  {
    kind := p.kind
    placement := p.placement
    content := content.split "\n" |>.toArray.map (·.toString)
  }
where
  normalizeContent (kind : Comment.Kind) (s : String.Slice) : String.Slice :=
    match kind with
    | .lineComment =>
      s.dropPrefix " " |>.dropSuffix "\n"
    | .blockComment =>
      s.dropPrefix " "
        |>.dropPrefix "\n"
        |>.dropSuffix "\n"
        |>.dropSuffix " "
  dropIndentation (line : String.Slice) (amount : Nat) : String.Slice := Id.run do
    let mut line := line
    let mut amount := amount
    while ! line.isEmpty && amount > 0 do
      let c := line.front
      if c != ' ' then
        break
      line := line.drop 1
      amount := amount - 1
    return line
  dropLinePrefix (line : String.Slice) : String.Slice := Id.run do
    let some pre := p.kind.linePrefix?
      | return line
    let some line := line.dropPrefix? pre
      | return line
    return line.dropPrefix " "

def advanceColumnOffset (columnOffset : Nat) (s : String.Slice) : Nat :=
  match s.revFind? '\n' with
  | none =>
    columnOffset + s.positions.length
  | some nlPos =>
    s.sliceFrom nlPos.next! |>.positions.length

def parseComments (trailingWs : String.Slice) (columnOffset : Nat) : Array Comment × Nat := Id.run do
  let kinds := #[Comment.Kind.lineComment, Comment.Kind.blockComment]

  let firstNewlinePos := trailingWs.find '\n' |>.str

  let mut trailingWs := trailingWs
  let mut columnOffset : Nat := columnOffset
  let mut comments : Array PendingComment := #[]

  let mut commentNestingLevel : Nat := 0
  let mut pendingComment? : Option PendingComment := none

  while ! trailingWs.isEmpty do
    match pendingComment? with
    | none =>
      let currentPos := trailingWs.startPos.str.offset
      let isAfterNewline := currentPos >= firstNewlinePos.offset
      let startMatch? := kinds.findSome? fun kind => do
        return (kind, ← trailingWs.dropPrefix? kind.startSymbol)
      if let some (kind, trailingWs') := startMatch? then
        pendingComment? := some {
          kind := kind
          placement := if isAfterNewline then .onLineBeforeToken else .afterToken
          full := kind.startSymbol
          content := #[]
          startColumnOffset := columnOffset
          startPos := currentPos
          endPos := currentPos + kind.startSymbol
        }
        commentNestingLevel := 1
        trailingWs := trailingWs'
        columnOffset := advanceColumnOffset columnOffset kind.startSymbol
        continue
      let c := trailingWs.front
      trailingWs := trailingWs.drop 1
      columnOffset := advanceColumnOffset columnOffset c.toString
      continue
    | some pendingComment =>
      let kind := pendingComment.kind
      let endMatch? := trailingWs.dropPrefix? kind.endSymbol
      if let some trailingWs' := endMatch? then
        commentNestingLevel := commentNestingLevel - 1
        let pendingComment := { pendingComment with
          full := pendingComment.full ++ kind.endSymbol
          endPos := pendingComment.endPos + kind.endSymbol
        }
        if !kind.hasNesting || commentNestingLevel == 0 then
          comments := comments.push pendingComment
          pendingComment? := none
        else
          pendingComment? := some pendingComment
        trailingWs := trailingWs'
        columnOffset := advanceColumnOffset columnOffset kind.endSymbol
        continue
      if kind.hasNesting then
        let startMatch? := trailingWs.dropPrefix? kind.startSymbol
        if let some trailingWs' := startMatch? then
          commentNestingLevel := commentNestingLevel + 1
          pendingComment? := some { pendingComment with
            full := pendingComment.full ++ kind.startSymbol
            endPos := pendingComment.endPos + kind.startSymbol
          }
          trailingWs := trailingWs'
          columnOffset := advanceColumnOffset columnOffset kind.startSymbol
          continue
      let c := trailingWs.front
      pendingComment? := some { pendingComment with
        full := pendingComment.full.push c
        endPos := pendingComment.endPos + c
      }
      trailingWs := trailingWs.drop 1
      columnOffset := advanceColumnOffset columnOffset c.toString
      continue
  if let some pendingComment := pendingComment? then
    if pendingComment.kind.endSymbol.all Char.isWhitespace then
      comments := comments.push pendingComment
      pendingComment? := none
  comments := groupComments comments
  let finalized := comments.map (·.finalize)
  return (finalized, columnOffset)
where
  groupComments (comments : Array PendingComment) : Array PendingComment := Id.run do
    if comments.isEmpty then
      return #[]
    let newlinePositions := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' trailingWs
      |>.filterMap fun
        | .matched startPos _ => some startPos.offset
        | .rejected .. => none
    let newlinePositions := newlinePositions.toArray
    let mut grouped := #[]
    let mut group := comments[0]!
    for c in comments[1:] do
      if !(group.kind matches .lineComment && c.kind matches .lineComment) then
        grouped := grouped.push group
        group := c
        continue
      let newlineBeforeC? := newlinePositions.binSearchRightmost c.startPos id (· < ·)
      if let some (_, newlineBeforeC) := newlineBeforeC? then
        if newlineBeforeC >= group.endPos then
          -- There is an empty line between `group` and `c`, which splits the group.
          grouped := grouped.push group
          group := c
          continue
      group := {
        kind := .lineComment
        placement := group.placement
        content := #[]
        full := group.full ++ c.full
        startColumnOffset := group.startColumnOffset
        startPos := group.startPos
        endPos := c.endPos
      }
    grouped := grouped.push group
    return grouped

structure collectComments.State where
  pendingComments : Array Comment := #[]
  comments : Std.HashMap Syntax.Range (Array Comment) := {}
  columnOffset : Nat := 0 -- TODO: init?

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

public def collectComments (stx : Syntax) :
    Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let (_, s) ← StateT.run (s := { : collectComments.State }) <| go stx
  return s.comments
where
  go (stx : Syntax) : collectComments.M Unit := do
    match stx with
    | .missing =>
      return
    | .atom info val =>
      collectTokenComments info val
    | .ident info rawVal .. =>
      let rawVal ← toSlice rawVal
      collectTokenComments info rawVal
    | .node _ _ args =>
      for arg in args do
        go arg
  collectTokenComments (info : SourceInfo) (tk : String.Slice) : collectComments.M Unit := do
    let some range := info.getRange?
      | throw <| .malformedInputSyntax stx (.ofSlice tk) "missing token range"
    let pendingComments ← modifyGet fun s =>
      (s.pendingComments, { s with pendingComments := #[] })
    addComments range pendingComments
    advanceColumnOffset tk
    let some trailing ← getTrailing? info
      | return
    let (comments, columnOffset) := parseComments trailing (← get).columnOffset
    let (commentsAfterToken, commentsOnLineBeforeToken) :=
      comments.partition (·.placement matches .afterToken)
    addComments range commentsAfterToken
    modify fun s => { s with
      pendingComments := s.pendingComments ++ commentsOnLineBeforeToken
      columnOffset
    }
    advanceColumnOffset trailing
  addComments (range : Syntax.Range) (newComments : Array Comment) : collectComments.M Unit := do
    modify fun s => { s with
      comments := s.comments.alter range fun
        | none => some newComments
        | some comments => some <| comments ++ newComments
    }
  advanceColumnOffset (val : String.Slice) : collectComments.M Unit :=
    modify fun s => { s with
      columnOffset := Fmt.advanceColumnOffset s.columnOffset val
    }
  toSlice (s : Substring.Raw) : collectComments.M String.Slice := do
    let some s := s.toSlice?
      | throw <| .malformedInputSyntax stx s
          "substring is invalid and cannot be converted to a slice"
    return s
  getTrailing? (info : SourceInfo) : collectComments.M (Option String.Slice) := do
    let some trailing := info.getTrailing?
      | return none
    toSlice trailing

end Extraction

section Placement

def reassociateComments
    {rendering : String.Slice}
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    Std.HashMap rendering.Subslice (Array Comment) := Id.run do
  let syntaxToRendered := RangeTree.ofHashMap syntaxToRendered
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => compareRanges a b == .lt)
  let mut r : Std.HashMap rendering.Subslice (Array Comment) := ∅
  for (commentRange, comments) in comments do
    let (_, ranges) := syntaxToRendered.findSmallestRangeContaining? commentRange |>.get!
    let range := findBestCommentRange ranges
    r := r.alter range fun
      | none => some comments
      | some previousComments => some <| previousComments ++ comments
  return r
where
  findBestCommentRange (ranges : Std.HashSet rendering.Subslice) : rendering.Subslice := Id.run do
    let ranges := ranges.toArray
    let mut bestRange := ranges[0]!
    let mut bestLength := bestRange.toSlice.chars.length
    for range in ranges[1:] do
      let length := range.toSlice.chars.length
      if length < bestLength || length == bestLength
          && range.startInclusive < bestRange.startInclusive then
        bestRange := range
        bestLength := length
    return bestRange

structure LineInfo (s : String.Slice) where
  length : Nat
  indentation : Nat
  range : s.Subslice
  deriving Inhabited

def collectLineInfos (s : String.Slice) : Array (LineInfo s) := Id.run do
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

def compareSubslicesLargest {s : String.Slice} (a b : s.Subslice) : Ordering :=
  Ord.compare a.startInclusive b.startInclusive
    |>.then (Ord.compare b.endExclusive a.endExclusive)

def determineCommentInsertions
    {rendering : String.Slice}
    (maxColumnWidth : Nat)
    (comments : Std.HashMap rendering.Subslice (Array Comment)) :
    Array (rendering.Pos × String) := Id.run do
  let lineInfos := collectLineInfos rendering
  -- We process comments from the back to the front
  -- (in the case of nested subslices, we process smaller subslices before larger ones).
  -- This ensures that we attempt to insert later comments on the same line first
  -- (after a token or at the end of the line) and when the line is full, earlier comments
  -- get moved before the line.
  let comments := comments.toArray.map fun (range, comments) => (range, comments.reverse)
  let comments := Std.TreeMap.ofArray comments (fun a b => compareSubslicesLargest b a)
  let mut lineLengths := lineInfos.map (·.length)
  let mut containsEndOfLineComments := Array.replicate lineInfos.size false
  let mut r : Std.HashMap rendering.Pos String  := ∅
  for (range, comments) in comments do
    for c in comments do
      let rps := c.renderedPlacements
      for rp in rps do
        match rp with
        | .afterClosestPreviousNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.startInclusive
          let insertionPos := lineInfo.range.startInclusive
          let insertedComment := c.toString.indent lineInfo.indentation ++ "\n"
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        | .beforeClosestNextNewline =>
          let (lineNum, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          if containsEndOfLineComments[lineNum]! then
            continue
          let lineLength := lineLengths[lineNum]!
          let insertionPos := lineInfo.range.endExclusive
          if r.contains insertionPos then
            continue
          let insertedComment := " " ++ c.toString
          let newLineLength := lineLength + insertedComment.length
          if newLineLength > maxColumnWidth then
            continue
          r := r.insert insertionPos insertedComment
          lineLengths := lineLengths.set! lineNum newLineLength
          containsEndOfLineComments := containsEndOfLineComments.set! lineNum true
        | .afterToken =>
          let (lineNum, _) := findLineInfoContaining lineInfos range.endExclusive
          let lineLength := lineLengths[lineNum]!
          let insertionPos := range.endExclusive
          let insertedComment :=
            if r.contains insertionPos then
              " " ++ c.toString
            else
              " " ++ c.toString ++ " "
          let newLineLength := lineLength + insertedComment.length
          if newLineLength > maxColumnWidth then
            continue
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
  return r.toArray.qsort (·.1 < ·.1)
where
  findLineInfoContaining (lineInfos : Array (LineInfo rendering)) (pos : rendering.Pos) : Nat × LineInfo rendering :=
    lineInfos.binSearchRightmost pos (·.range.startInclusive) (· < ·) |>.get!

public def insertComments
    (maxColumnWidth : Nat)
    (rendering : String.Slice)
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    String := Id.run do
  let comments := reassociateComments syntaxToRendered comments
  let insertions := determineCommentInsertions maxColumnWidth comments
  let mut r : String := ""
  let mut startPos : rendering.Pos := rendering.startPos
  for (insertionPos, comments) in insertions do
    r := r ++ rendering.slice! startPos insertionPos
    r := r ++ comments
    startPos := insertionPos
  return r

end Placement
