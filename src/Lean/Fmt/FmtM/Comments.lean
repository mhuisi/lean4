/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Syntax
public import Lean.Fmt.FmtM.Error
public import Lean.Fmt.Util.Basic
import Lean.Fmt.Util.RangeTree
import Init.Data.String.Search
import Init.Control.Basic
public import Lean.Fmt.FmtM.LineInfo

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
  deriving Inhabited, BEq, Repr

/-- Comment placement in the input `Syntax`. -/
public inductive Comment.Placement where
  | afterToken
  | onLineBeforeToken
  deriving Inhabited, BEq, Repr

/-- Kind of comment in the input `Syntax`. -/
public inductive Comment.Kind where
  | lineComment
  | blockComment
  deriving Inhabited, BEq, Repr

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
  of the comment relative to the least indented line with content in the comment.
  -/
  content : Array String
  deriving Inhabited, BEq, Repr

public structure Comment.Rendering where
  rendered : String
  isMultiLine : Bool
  deriving Inhabited

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
public inductive Comment.RenderedPlacementKind where
  /-- Placed on a separate line before the token that this comment is attached to. -/
  | afterClosestPreviousNewline
  /-- Placed on the end of the same line as the token that this comment is attached to. -/
  | beforeClosestNextNewline
  | afterToken

structure Comment.RenderedPlacement where
  kind : RenderedPlacementKind
  rendering : Rendering

/--
Yields a set of alternative placements of this comment in a rendered output, sorted descendingly
by priority.
If a specific placement cannot be placed into the line it is placed at, a lower priority placement
is preferred.
Ensures that the lowest priority placement can always be placed into a line.
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
      | .blockComment, .afterToken =>
        if rendering.isMultiLine then
          #[.afterClosestPreviousNewline]
        else
          #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
      | .blockComment, .onLineBeforeToken =>
        #[.afterClosestPreviousNewline]
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
removing start, end and line separators, erasing all indentation relative to the least indented
line with content in the comment and dropping stylistic whitespace at the start and the end of the
comment (e.g. the separation space in `-- ` or the newlines in a multi-line `/-\n...\n-/`).
-/
def PendingComment.finalize (p : PendingComment) : Comment :=
  let s := p.raw.toSlice.dropPrefix p.kind.startSymbol
    |>.dropSuffix p.kind.endSymbol
  let lines := s.split "\n" |>.toArray
  let indentation := contentColumnOffset lines
  let deindentedLines :=
    lines[0]! ::
      (lines[1:].toList.map (dropIndentation · indentation) |>.map dropLinePrefix)
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
  contentColumnOffset (lines : Array String.Slice) : Nat := Id.run do
    let mut offset? : Option Nat := none
    for (line, i) in lines.zipIdx do
      let indentation := line.takeWhile (· == ' ') |>.chars.length
      if indentation == line.chars.length then
        continue
      let lineColumnOffset :=
        if i == 0 then p.startColumnOffset + p.kind.startSymbol.chars.length else 0
      let columnOffset := lineColumnOffset + indentation
      offset? := some <| match offset? with
        | none => columnOffset
        | some offset => min offset columnOffset
    return offset?.getD p.startColumnOffset
  normalizeContent (kind : Comment.Kind) (s : String.Slice) : String.Slice := Id.run do
    match kind with
    | .lineComment =>
      s.dropPrefix " " |>.dropSuffix "\n"
    | .blockComment =>
      s.dropWhile (fun c => c = ' ' || c = '\n')
        |>.dropEndWhile (fun c => c = ' ' || c = '\n')
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
    let (_, commentStartLineInfo) := binSearchRightmost lineInfos commentRawStartPos (·.startPos) (· < ·) |>.get!
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
      if ! isGroupable newlinePositions group c then
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

  isGroupable (newlinePositions : Array String.Pos.Raw) (group c : PendingComment) : Bool := Id.run do
    let isGroupableKind := group.kind matches .lineComment && c.kind matches .lineComment
    if ! isGroupableKind then
      return false
    let isGroupablePlacement :=
      match group.placement, c.placement with
      | .onLineBeforeToken, .onLineBeforeToken
      | .afterToken, .afterToken =>
        true
      | .afterToken, .onLineBeforeToken =>
        group.startColumnOffset == c.startColumnOffset
      | .onLineBeforeToken, .afterToken =>
        false
    if ! isGroupablePlacement then
      return false
    let newlineBeforeC? := binSearchRightmost newlinePositions c.startPos id (· < ·)
    let isGroupableAdjacency :=
      if let some (_, newlineBeforeC) := newlineBeforeC? then
        -- There is an empty line between `group` and `c`, which splits the group.
        newlineBeforeC < group.endPos
      else
        true
    if ! isGroupableAdjacency then
      return false
    return true

structure collectComments.State where
  pendingComments : Array Comment := #[]
  comments : Std.HashMap Syntax.Range (Array Comment) := {}

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

/--
Collects all comments in `stx`, associating them either with the token immediately before a comment
on the same line or if the comment is on its own line with the next token following the comment.
-/
public partial def collectComments (lineInfos : Array SyntaxLineInfo) (stx : Syntax) :
    Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let (_, s) ← StateT.run (s := { : collectComments.State }) <| go stx
  -- Comments on lines after the last token (i.e. `s.pendingComments`) are ignored.
  -- When formatting entire files, there is always an `eoi` token at the end
  -- (so `s.pendingComments` is empty) and when formatting parts of files,
  -- we always want to ignore those comments anyways.
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
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg
  collectTokenComments (info : SourceInfo) (_tk : String.Slice) : collectComments.M Unit := do
    let some range := info.getRange?
      | -- throw <| .malformedInputSyntax stx (some <| .ofSlice tk) "missing token range"
        -- TODO: Replace with throwing an exception when Verso docstrings are fixed.
        -- Currently, Verso docstrings violate this assumption because they are being elaborated
        -- *in the parser*.
        return
    if let some leading ← info.getLeading? |>.mapM toSlice then
      let comments := parseComments lineInfos range .leading leading
      modify fun s => { s with
        pendingComments := s.pendingComments ++ comments
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
    for newComment in newComments do
      let range :=
        match newComment.kind, newComment.placement with
        | .lineComment, .afterToken
        | .blockComment, .afterToken =>
          if newComment.content.size > 1 then
            let (_, commentStartLineInfo) := binSearchRightmost lineInfos newComment.originalWhitespaceRange.start (·.startPos) (· < ·) |>.get!
            commentStartLineInfo.tokenRanges[0]!
          else
            range
        | _, _ =>
          range
      modify fun s => { s with
        comments := s.comments.alter range fun
          | none => some #[newComment]
          | some comments => some <| comments.push newComment
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
      |>.then (Ord.compare b.bsize a.bsize)
    ord.isLT
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => Lean.Fmt.compareRanges a b == .lt)
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
    -- In this case, we re-associate comments before a token and line comments after a token
    -- with the closest range after the token and block comments after a token with the closest
    -- range before the token.
    let (commentsWithPreviousRangeFallback, commentsWithNextRangeFallback) :=
      comments.partition fun c => c.content.size <= 1 && c.placement matches .afterToken
    let (_, _, rangesForPreviousRangeFallback) :=
      binSearchRightmost syntaxToRenderedByStop range.stop (·.1.stop) (· < ·) |>.get!
    let (_, _, rangesForNextRangeFallback) :=
      binSearchLeftmost syntaxToRenderedByStart range.start (·.1.start) (· < ·) |>.get!
    return #[
      (findBestCommentRange rangesForPreviousRangeFallback, commentsWithPreviousRangeFallback),
      (findBestCommentRange rangesForNextRangeFallback, commentsWithNextRangeFallback),
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
  let mut containsEndOfLineComments := lineInfos.map (·.range.toSlice.contains "--")
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
          let newLineLength := insertedComment.chars.length - 1
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
          let newLineLength := lineLength + insertedComment.chars.length
          if ! isFinalAlternative && newLineLength > maxColumnWidth then
            continue
          r := r.insert insertionPos insertedComment
          lineLengths := lineLengths.set! lineNum newLineLength
          if c.kind matches .lineComment then
            containsEndOfLineComments := containsEndOfLineComments.set! lineNum true
        | .afterToken =>
          unreachable!
        break
  return r.toArray.qsort (·.1 < ·.1)
where
  findLineInfoContaining (lineInfos : Array (LineInfo rendering)) (pos : rendering.Pos) : Nat × LineInfo rendering :=
    binSearchRightmost lineInfos pos (·.range.startInclusive) (· < ·) |>.get!

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
