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
  | onLineAfterToken
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
  /-- Placed on a separate line before the token that this comment is attached to. -/
  | afterClosestPreviousNewline
  /-- Placed on the end of the same line as the token that this comment is attached to. -/
  | beforeClosestNextNewline
  /-- Placed directly after the token that this comment is attached to. -/
  | afterToken
  /-- Placed on a separate line after the token that this comment is attached to. -/
  | afterClosestNextNewline

/-- Comment extracted from an input `Syntax`. -/
public structure Comment where
  /-- Kind of comment in the input `Syntax`. -/
  kind : Comment.Kind
  /-- Comment placement in the input `Syntax`. -/
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
  | .lineComment, .onLineAfterToken =>
    #[.afterClosestNextNewline]
  | .blockComment, .afterToken =>
    if isMultiLine then
      #[.afterClosestPreviousNewline]
    else
      #[.afterToken, .afterClosestPreviousNewline]
  | .blockComment, .onLineBeforeToken =>
    #[.afterClosestPreviousNewline]
  | .blockComment, .onLineAfterToken =>
    #[.afterClosestNextNewline]

section Extraction

structure PendingComment extends Comment where
  raw : String
  startColumnOffset : Nat
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited

/--
Finalizes a pending comment, extracting `Comment.content` from `PendingComment.raw` by
removing start, end and line separators, erasing all indentation relative to the start separator
and dropping stylistic whitespace at the start and the end of the comment
(e.g. the separation space in `-- ` or the newlines in a multi-line `/-\n...\n-/`).
-/
def PendingComment.finalize (p : PendingComment) : Comment :=
  let s := p.raw.toSlice.dropPrefix p.kind.startSymbol
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

/--
Advances `columnOffset` by pretending that `s` is appended at `columnOffset`.
If `s` contains newlines, `columnOffset` is reset to 0 at the last newline in `s` and advanced
from there with the remainder of `s`.
-/
def advanceColumnOffset (columnOffset : Nat) (s : String.Slice) : Nat :=
  match s.revFind? '\n' with
  | none =>
    columnOffset + s.positions.length
  | some nlPos =>
    s.sliceFrom nlPos.next! |>.positions.length

structure parseComments.State where
  -- Read-only
  firstNewlinePos : String.Pos.Raw

  -- State
  trailingWs : String.Slice
  columnOffset : Nat
  closedComments : Array PendingComment
  openComment? : Option PendingComment
  commentNestingLevel : Nat

/--
Parses the comments in `initialTrailingWs` at a current column offset of `initialColumnOffset`.
Yields the set of comments and the column offset after `initialTailingWs`.
-/
def parseComments
    (initialTrailingWs : String.Slice)
    (initialColumnOffset : Nat) :
    Array Comment × Nat := Id.run do
  let (_, s) := StateT.run go {
    firstNewlinePos := initialTrailingWs.find '\n' |>.str.offset
    trailingWs := initialTrailingWs
    columnOffset := initialColumnOffset
    closedComments := #[]
    openComment? := none
    commentNestingLevel := 0
  }
  let comments := groupComments s.closedComments
  let finalized := comments.map (·.finalize)
  return (finalized, s.columnOffset)

where

  go : StateM parseComments.State Unit := do
    let kinds := #[Comment.Kind.lineComment, Comment.Kind.blockComment]
    while ! (← get).trailingWs.isEmpty do
      match (← get).openComment? with
      | none =>
        let mut anySuccess := false
        for kind in kinds do
          let success ← tryOpenComment kind
          if success then
            anySuccess := true
            break
        if ! anySuccess then
          skip
      | some _openComment =>
        let success ← tryCloseComment
        if success then
          continue
        let success ← tryNestComment
        if success then
          continue
        skip
    terminateEndOfWhitespaceComment

  advanceBy (pre : String) : StateM parseComments.State Unit := do
    modify fun s => { s with
      trailingWs := s.trailingWs.dropPrefix pre
      columnOffset := advanceColumnOffset s.columnOffset pre
      openComment? := s.openComment?.map fun openComment =>
        { openComment with
          raw := openComment.raw ++ pre
          endPos := openComment.endPos + pre
        }
    }

  skip : StateM parseComments.State Unit := do
    let some c := (← get).trailingWs.front?
      | return
    advanceBy c.toString

  tryParse (pat : String) : StateM parseComments.State Bool := do
    if ! (← get).trailingWs.startsWith pat then
      return false
    advanceBy pat
    return true

  tryOpenComment
      (kind : Comment.Kind) :
      StateM parseComments.State Bool := do
    let commentStartPos := (← get).trailingWs.startPos.str.offset
    let isAfterNewline := commentStartPos >= (← get).firstNewlinePos
    let commentStartColumnOffset := (← get).columnOffset
    let success ← tryParse kind.startSymbol
    if ! success then
      return false
    modify fun s => { s with
      openComment? := some {
        kind
        placement := if isAfterNewline then .onLineBeforeToken else .afterToken
        raw := kind.startSymbol
        content := #[]
        startColumnOffset := commentStartColumnOffset
        startPos := commentStartPos
        endPos := commentStartPos + kind.startSymbol
      }
      commentNestingLevel := 1
    }
    return true

  tryCloseComment : StateM parseComments.State Bool := do
    let some openComment := (← get).openComment?
      | return false
    let kind := openComment.kind
    let success ← tryParse kind.endSymbol
    if ! success then
      return false
    let closedComment := (← get).openComment?.get!
    let commentNestingLevel := (← get).commentNestingLevel - 1
    if ! kind.hasNesting || commentNestingLevel == 0 then
      modify fun s => { s with
        closedComments := s.closedComments.push closedComment
        openComment? := none
      }
    else
      modify fun s => { s with
        openComment? := some closedComment
      }
    return true

  tryNestComment : StateM parseComments.State Bool := do
    let some openComment := (← get).openComment?
      | return false
    let kind := openComment.kind
    if ! kind.hasNesting then
      return false
    let success ← tryParse kind.startSymbol
    if ! success then
      return false
    modify fun s => { s with
      commentNestingLevel := s.commentNestingLevel + 1
    }
    return true

  terminateEndOfWhitespaceComment : StateM parseComments.State Unit := do
    let some openComment := (← get).openComment?
      | return
    if ! openComment.kind.endSymbol.all Char.isWhitespace then
      return
    let closedComment := openComment
    modify fun s => { s with
      closedComments := s.closedComments.push closedComment
      openComment? := none
    }

  groupComments (comments : Array PendingComment) : Array PendingComment := Id.run do
    if comments.isEmpty then
      return #[]
    let newlinePositions := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' initialTrailingWs
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
        -- This is strictly speaking not a proper `raw` representation for the entire group,
        -- since it does not contain the whitespace in-between `group` and `c`,
        -- but this is not a problem since `PendingComment.finalize` can handle this disparity.
        raw := group.raw ++ c.raw
        startColumnOffset := group.startColumnOffset
        startPos := group.startPos
        endPos := c.endPos
      }
    grouped := grouped.push group
    return grouped

structure collectComments.State where
  pendingComments : Array Comment := #[]
  comments : Std.HashMap Syntax.Range (Array Comment) := {}
  columnOffset : Nat
  lastTokenRange? : Option Syntax.Range := none

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

/--
Collects all comments in `stx`, associating them either with the token immediately before a comment
on the same line or if the comment is on its own line with the next token following the comment.
-/
public def collectComments (stx : Syntax) (offset : Nat := 0):
    Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let (_, s) ← StateT.run (s := { columnOffset := offset : collectComments.State }) <| go stx
  let some lastTokenRange := s.lastTokenRange?
    | throw <| .emptyInputSyntax stx
  let endOfFileComments := s.pendingComments.map fun c => { c with
    placement := .onLineAfterToken
  }
  let mut comments := s.comments
  if ! endOfFileComments.isEmpty then
    comments := comments.alter lastTokenRange fun
      | none => some endOfFileComments
      | some comments => some <| comments ++ endOfFileComments
  return comments
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
    modify fun s => { s with
      lastTokenRange? := some range
    }
    let pendingComments ← modifyGet fun s =>
      (s.pendingComments, { s with pendingComments := #[] })
    addComments range pendingComments
    modify fun s => { s with
      columnOffset := Fmt.advanceColumnOffset s.columnOffset tk
    }
    let some trailing ← info.getTrailing? |>.mapM toSlice
      | return
    let (comments, columnOffset) := parseComments trailing (← get).columnOffset
    let (commentsAfterToken, commentsOnLineBeforeToken) :=
      comments.partition (·.placement matches .afterToken)
    addComments range commentsAfterToken
    modify fun s => { s with
      pendingComments := s.pendingComments ++ commentsOnLineBeforeToken
      columnOffset
    }
  addComments (range : Syntax.Range) (newComments : Array Comment) : collectComments.M Unit := do
    if newComments.isEmpty then
      return
    modify fun s => { s with
      comments := s.comments.alter range fun
        | none => some newComments
        | some comments => some <| comments ++ newComments
    }
  toSlice (s : Substring.Raw) : collectComments.M String.Slice := do
    let some s := s.toSlice?
      | throw <| .malformedInputSyntax stx s
          "substring is invalid and cannot be converted to a slice"
    return s

end Extraction

section Placement

/--
Associates every comment with a specific range in the rendered output.
If the token that a comment is attached to is rendered in the output,
the comment will be associated with the rendered token.
If the token that a comment is attached to is not rendered,
the comments are associated with the smallest parent range of the token they are attached to that
is rendered.
If a specific range is rendered several times, we choose the smallest rendered range to attach
the comment to, so as to not duplicate the comment.
-/
def reassociateComments
    {rendering : String.Slice}
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    Std.HashMap rendering.Subslice (Array Comment) := Id.run do
  let syntaxToRendered := RangeTree.ofHashMap syntaxToRendered
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => compareRanges a b == .lt)
  let mut r : Std.HashMap rendering.Subslice (Array Comment) := ∅
  for (range, comments) in comments do
    let (_, ranges) := syntaxToRendered.findSmallestRangeContaining? range |>.get!
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

/--
For every line in `s`, determines the length of the line in characters, the level of indentation
and the range of the line (without the terminal `\n`).
-/
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
      for rp in c.renderedPlacements do
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
          let insertedComment := " " ++ c.toString
          let newLineLength := lineLength + insertedComment.length
          if newLineLength > maxColumnWidth then
            continue
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        | .afterClosestNextNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          -- `lineInfo.range.endExclusive.next?` is only `none` on EOF, in which case we insert
          -- the comment at the end of the file.
          let insertionPos := lineInfo.range.endExclusive.next? |>.getD lineInfo.range.endExclusive
          let insertedComment := "\n" ++ c.toString.indent lineInfo.indentation
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        break
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
    if let some charAfterComment := insertionPos.get? then
      let endCommentChar := comments.revChars.first?.get!
      if ! endCommentChar.isWhitespace && ! charAfterComment.isWhitespace then
        -- Padding after `comments`
        r := r ++ " "
    startPos := insertionPos
  r := r ++ rendering.slice! startPos rendering.endPos
  return r

end Placement
