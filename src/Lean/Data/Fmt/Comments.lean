/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Syntax
public import Lean.Data.Fmt.Error
public import Lean.Data.Fmt.Util
import Lean.Data.Fmt.RangeTree
import Lean.Data.Fmt.LineInfo
import Init.Data.String.Search
import Init.Control.Basic
public import Lean.Data.Fmt.LineInfo

/-- Indents all lines in `s` by `numSpaces` spaces. -/
def String.indent (s : String) (numSpaces : Nat) : String :=
  s.split "\n"
    |>.map (fun line => "".pushn ' ' numSpaces ++ line.toString)
    |>.toList
    |> "\n".intercalate

namespace Lean.Fmt

/-- Whether the comment was placed in leading or trailing whitespace in the input `Syntax`. -/
public inductive Comment.Whitespace where
  | leading
  | trailing
  deriving Inhabited, Repr

/-- Comment placement in the input `Syntax`. -/
public inductive Comment.Placement where
  | afterToken
  | onLineBeforeToken
  | onLineAfterToken
  deriving Inhabited, BEq, Repr

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


/-- Comment extracted from an input `Syntax`. -/
public structure Comment where
  /-- Kind of comment in the input `Syntax`. -/
  kind : Comment.Kind
  /-- Comment placement in the input `Syntax`. -/
  placement : Comment.Placement
  /-- Range of the original token in the input `Syntax` that this comment was attached to. -/
  originalTokenRange : Syntax.Range
  /-- Range of the trailing whitespace in the input `Syntax`. -/
  originalWhitespaceRange : Syntax.Range
  /-- Whether the comment was placed in leading or trailing whitespace in the input `Syntax`. -/
  originalWhitespaceKind : Comment.Whitespace
  /--
  Content of the comment separated into lines.
  Excludes the comment separators and all whitespace within the comment that serves as indentation
  of the comment relative to the start symbol of the comment.
  -/
  content : Array String
  deriving Inhabited, Repr

public structure Comment.Rendering where
  rendered : String
  isMultiLine : Bool

/--
Renders this comment to a set of string alternatives, sorted descendingly by priority.
If a specific rendering does not fit into the line it is placed at, a lower priority rendering is
preferred.
-/
public def Comment.render (c : Comment) : Array Rendering :=
  match c.kind with
  | .lineComment =>
    let lines := c.content.map fun content =>
      if content.chars.all (· == '-') then
        s!"--{content}"
      else
        s!"-- {content}"
    #[⟨lines.toList |> "\n".intercalate, lines.size > 1⟩]
  | .blockComment =>
    let singleLineRendering :=
      if c.content[0]!.chars.all (· == '-') then
        s!"/-{c.content[0]!}-/"
      else
        s!"/- {c.content[0]!} -/"
    let multiLineRendering :=
      s!"/-\n{"\n".intercalate c.content.toList}\n-/"
    if c.content.size == 1 then
      #[⟨singleLineRendering, false⟩, ⟨multiLineRendering, true⟩]
    else
      #[⟨multiLineRendering, true⟩]

/-- Where this comment should be placed in the rendered document. -/
inductive Comment.RenderedPlacementKind where
  /-- Placed on a separate line before the token that this comment is attached to. -/
  | afterClosestPreviousNewline
  /-- Placed on the end of the same line as the token that this comment is attached to. -/
  | beforeClosestNextNewline
  /-- Placed directly after the token that this comment is attached to. -/
  | afterToken
  /-- Placed on a separate line after the token that this comment is attached to. -/
  | afterClosestNextNewline

structure Comment.RenderedPlacement where
  kind : RenderedPlacementKind
  rendering : Rendering

/--
Yields a set of alternative placements of this comment in a rendered output, sorted descendingly
by priority.
If a specific placement does not fit into the line it is placed at, a lower priority placement
is preferred.
Ensures that the lowest priority placement always fits into a line.
-/
def Comment.renderedPlacements (c : Comment) : Array RenderedPlacement :=
  c.render.flatMap fun rendering =>
    let kinds : Array RenderedPlacementKind :=
      match c.kind, c.placement with
      | .lineComment, .afterToken =>
        if rendering.isMultiLine then
          #[.afterClosestPreviousNewline]
        else
          #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
      | .lineComment, .onLineBeforeToken =>
        #[.afterClosestPreviousNewline]
      | .lineComment, .onLineAfterToken =>
        #[.afterClosestNextNewline]
      | .blockComment, .afterToken =>
        if rendering.isMultiLine then
          #[.afterClosestPreviousNewline]
        else
          #[.afterToken, .afterClosestPreviousNewline]
      | .blockComment, .onLineBeforeToken =>
        #[.afterClosestPreviousNewline]
      | .blockComment, .onLineAfterToken =>
        #[.afterClosestNextNewline]
    kinds.map (⟨·, rendering⟩)

section Extraction

structure PendingComment extends Comment where
  raw : String
  startColumnOffset : Nat
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited, Repr

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
    originalTokenRange := p.originalTokenRange
    originalWhitespaceRange := ⟨p.startPos, p.endPos⟩
    originalWhitespaceKind := p.originalWhitespaceKind
    content := content.split "\n" |>.toArray.map (·.toString)
  }
where
  normalizeContent (kind : Comment.Kind) (s : String.Slice) : String.Slice :=
    match kind with
    | .lineComment =>
      s.dropPrefix " " |>.dropSuffix "\n"
    | .blockComment =>
      s.dropWhile ' '
        |>.dropPrefix "\n"
        |>.dropEndWhile " "
        |>.dropSuffix "\n"
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
  ws : String.Slice
  closedComments : Array PendingComment
  openComment? : Option PendingComment
  commentNestingLevel : Nat

/--
Parses the comments in `initialWs` at a current column offset of `initialColumnOffset`.
Yields the set of comments and the column offset after `initialWs`.
-/
public def parseComments
    (lineInfos : Array SyntaxLineInfo)
    (originalTokenRange : Syntax.Range)
    (originalWhitespaceKind : Comment.Whitespace)
    (initialWs : String.Slice) :
    Array Comment := Id.run do
  let (_, s) := StateT.run go {
    firstNewlinePos := initialWs.find '\n' |>.str.offset
    ws := initialWs
    closedComments := #[]
    openComment? := none
    commentNestingLevel := 0
  }
  let comments := groupComments s.closedComments
  let finalized := comments.map (·.finalize)
  return finalized

where

  go : StateM parseComments.State Unit := do
    let kinds := #[Comment.Kind.lineComment, Comment.Kind.blockComment]
    while ! (← get).ws.isEmpty do
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
      ws := s.ws.dropPrefix pre
      openComment? := s.openComment?.map fun openComment =>
        { openComment with
          raw := openComment.raw ++ pre
          endPos := openComment.endPos + pre
        }
    }

  skip : StateM parseComments.State Unit := do
    let some c := (← get).ws.front?
      | return
    advanceBy c.toString

  tryParse (pat : String) : StateM parseComments.State Bool := do
    if ! (← get).ws.startsWith pat then
      return false
    advanceBy pat
    return true

  tryOpenComment
      (kind : Comment.Kind) :
      StateM parseComments.State Bool := do
    let ws := (← get).ws
    let commentStartPos := ws.startPos.str
    let commentRawStartPos := commentStartPos.offset
    let (_, commentStartLineInfo) := lineInfos.binSearchRightmost commentRawStartPos (·.startPos) (· < ·) |>.get!
    let commentLineStartPos := ws.str.pos! commentStartLineInfo.startPos
    let commentStartColumnOffset := ws.str.slice! commentLineStartPos commentStartPos |>.chars.length
    let isAfterNewline := commentRawStartPos >= (← get).firstNewlinePos
    let success ← tryParse kind.startSymbol
    if ! success then
      return false
    modify fun s => { s with
      openComment? := some {
        kind
        placement :=
          if originalWhitespaceKind matches .leading || isAfterNewline then
            .onLineBeforeToken
          else
            .afterToken
        originalTokenRange
        originalWhitespaceRange := ⟨0, 0⟩
        originalWhitespaceKind
        raw := kind.startSymbol
        content := #[]
        startColumnOffset := commentStartColumnOffset
        startPos := commentRawStartPos
        endPos := commentRawStartPos + kind.startSymbol
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
        commentNestingLevel
      }
    else
      modify fun s => { s with
        openComment? := some closedComment
        commentNestingLevel
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
    if ! openComment.kind.endSymbol.chars.all Char.isWhitespace then
      return
    let closedComment := openComment
    modify fun s => { s with
      closedComments := s.closedComments.push closedComment
      openComment? := none
    }

  groupComments (comments : Array PendingComment) : Array PendingComment := Id.run do
    if comments.isEmpty then
      return #[]
    let newlinePositions := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' initialWs
      |>.filterMap fun
        | .matched startPos _ => some startPos.str.offset
        | .rejected .. => none
    let newlinePositions := newlinePositions.toArray
    let mut grouped := #[]
    let mut group := comments[0]!
    for c in comments[1:] do
      if !(group.kind matches .lineComment && c.kind matches .lineComment) then
        grouped := grouped.push group
        group := c
        continue
      if group.placement != c.placement then
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
        originalTokenRange := group.originalTokenRange
        originalWhitespaceRange :=
          ⟨group.originalWhitespaceRange.start, c.originalWhitespaceRange.stop⟩
        originalWhitespaceKind := group.originalWhitespaceKind
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
  lastTokenRange? : Option Syntax.Range := none

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

/--
Collects all comments in `stx`, associating them either with the token immediately before a comment
on the same line or if the comment is on its own line with the next token following the comment.
-/
public partial def collectComments (lineInfos : Array SyntaxLineInfo) (stx : Syntax) :
    Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let (_, s) ← StateT.run (s := { : collectComments.State }) <| go stx
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
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg
  collectTokenComments (info : SourceInfo) (tk : String.Slice) : collectComments.M Unit := do
    let some range := info.getRange?
      | throw <| .malformedInputSyntax stx (some <| .ofSlice tk) "missing token range"
    if let some leading ← info.getLeading? |>.mapM toSlice then
      let comments := parseComments lineInfos range .leading leading
      modify fun s => { s with
        pendingComments := s.pendingComments ++ comments
      }
    modify fun s => { s with
      lastTokenRange? := some range
    }
    let pendingComments ← modifyGet fun s =>
      (s.pendingComments, { s with pendingComments := #[] })
    addComments range pendingComments
    if let some trailing ← info.getTrailing? |>.mapM toSlice then
      let comments := parseComments lineInfos range .trailing trailing
      let (commentsAfterToken, commentsOnLineBeforeToken) :=
        comments.partition (·.placement matches .afterToken)
      addComments range commentsAfterToken
      modify fun s => { s with
        pendingComments := s.pendingComments ++ commentsOnLineBeforeToken
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
the comments are associated with the next range before or after the token, depending on the
placement of the comment in the syntax.
If a specific range is rendered several times, we choose the smallest rendered range to attach
the comment to, so as to not duplicate the comment.
-/
def reassociateComments
    {rendering : String.Slice}
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment)) :
    Std.HashMap rendering.Subslice (Array Comment) := Id.run do
  let syntaxToRenderedByStart := syntaxToRendered.toArray.qsort fun (a, _) (b, _) =>
    let ord := (Ord.compare a.start b.start)
      |>.then (Ord.compare a.bsize b.bsize)
    ord.isLT
  let syntaxToRenderedByStop := syntaxToRendered.toArray.qsort fun (a, _) (b, _) =>
    let ord := (Ord.compare a.stop b.stop)
      |>.then (Ord.compare a.bsize b.bsize)
    ord.isLT
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => compareRanges a b == .lt)
  let mut r : Std.HashMap rendering.Subslice (Array Comment) := ∅
  for (range, comments) in comments do
    let renderedCommentRanges := determineRenderedCommentRanges
      syntaxToRenderedByStart
      syntaxToRenderedByStop
      range
      comments
    for (renderedRange, comments) in renderedCommentRanges do
      r := r.alter renderedRange fun
        | none => some comments
        | some previousComments => some <| previousComments ++ comments
  return r
where
  determineRenderedCommentRanges
      (syntaxToRenderedByStart : Array (Syntax.Range × Std.HashSet rendering.Subslice))
      (syntaxToRenderedByStop : Array (Syntax.Range × Std.HashSet rendering.Subslice))
      (range : Syntax.Range)
      (comments : Array Comment)
      : Array (rendering.Subslice × Array Comment) := Id.run do
    if let some exactCommentRanges := syntaxToRendered.get? range then
      return #[(findBestCommentRange exactCommentRanges, comments)]
    -- If one of the formatters removed the token
    -- (or did not accurately track the `ref` for every `Doc.text` node)
    -- then we may not find an exact syntax match.
    -- In this case, we re-associate comments before a token with the closest range after the token
    -- and comments after a token with the closest range before the token.
    let (commentsBeforeToken, commentsAfterToken) :=
      comments.partition (·.placement matches .onLineBeforeToken)
    let (_, _, rangesForCommentsBeforeToken) :=
      syntaxToRenderedByStart.binSearchLeftmost range.start (·.1.start) (· < ·) |>.get!
    let (_, _, rangesForCommentsAfterToken) :=
      syntaxToRenderedByStop.binSearchRightmost range.stop (·.1.stop) (· < ·) |>.get!

    return #[
      (findBestCommentRange rangesForCommentsBeforeToken, commentsBeforeToken),
      (findBestCommentRange rangesForCommentsAfterToken, commentsAfterToken),
    ]

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
      for (rp, i) in c.renderedPlacements.zipIdx do
        let isFinalAlternative := i == c.renderedPlacements.size - 1
        match rp.kind with
        | .afterClosestPreviousNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.startInclusive
          let insertionPos := lineInfo.range.startInclusive
          let insertedComment := rp.rendering.rendered.indent lineInfo.indentation ++ "\n"
          let newLineLength := insertedComment.length - 1
          if ! isFinalAlternative && newLineLength > maxColumnWidth then
            continue
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        | .beforeClosestNextNewline =>
          let (lineNum, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          if containsEndOfLineComments[lineNum]! then
            assert! ! isFinalAlternative
            continue
          let lineLength := lineLengths[lineNum]!
          let insertionPos := lineInfo.range.endExclusive
          if r.contains insertionPos then
            assert! ! isFinalAlternative
            continue
          let insertedComment := " " ++ rp.rendering.rendered
          let newLineLength := lineLength + insertedComment.length
          if ! isFinalAlternative && newLineLength > maxColumnWidth then
            continue
          r := r.insert insertionPos insertedComment
          lineLengths := lineLengths.set! lineNum newLineLength
          containsEndOfLineComments := containsEndOfLineComments.set! lineNum true
        | .afterToken =>
          let (lineNum, _) := findLineInfoContaining lineInfos range.endExclusive
          let lineLength := lineLengths[lineNum]!
          let insertionPos := range.endExclusive
          let insertedComment := " " ++ rp.rendering.rendered
          let newLineLength := lineLength + insertedComment.length
          if ! isFinalAlternative && newLineLength > maxColumnWidth then
            continue
          r := r.alter insertionPos fun
            | none => some insertedComment
            | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        | .afterClosestNextNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          -- `lineInfo.range.endExclusive.next?` is only `none` on EOF, in which case we insert
          -- the comment at the end of the file.
          let insertionPos := lineInfo.range.endExclusive.next? |>.getD lineInfo.range.endExclusive
          let insertedComment := "\n" ++ rp.rendering.rendered.indent lineInfo.indentation
          let newLineLength := insertedComment.length - 1
          if ! isFinalAlternative && newLineLength > maxColumnWidth then
            continue
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
