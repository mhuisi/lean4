import Lean.Fmt.FmtM.LineInfo

/-!
Tests the line information collected by the auto-formatter: `collectLineInfos`,
`collectSyntaxLineInfos` and `collectSyntaxLineInfos'`.
-/

open Lean Lean.Fmt

-- Extracts (length, indentation, text) for each line.
def lineInfoData (s : String) : Array (Nat × Nat × String) :=
  (collectLineInfos s.toSlice).map fun info =>
    (info.length, info.indentation, info.range.toString)

-- Extracts (length, indentation, line, startPos.byteIdx, endPos.byteIdx) for each line.
def syntaxLineInfoData (stx : Lean.Syntax) : Array (Nat × Nat × String × Nat × Nat) :=
  (collectSyntaxLineInfos stx).map fun info =>
    (info.length, info.indentation, info.line, info.startPos.byteIdx, info.endPos.byteIdx)

-- Extracts (start.byteIdx, stop.byteIdx) of every token range of every line.
def syntaxLineTokenData (stx : Lean.Syntax) : Array (Array (Nat × Nat)) :=
  (collectSyntaxLineInfos stx).map fun info =>
    info.tokenRanges.map fun range => (range.start.byteIdx, range.stop.byteIdx)

-- Constructs an atom with the given value and trailing whitespace.
private def mkAtomTrailing (val trailing : String) : Lean.Syntax :=
  .atom (SourceInfo.original "".toRawSubstring ⟨0⟩ trailing.toRawSubstring ⟨0⟩) val

-- ===== collectLineInfos =====

-- Empty string: one line with length 0 and empty range.
#guard lineInfoData "" = #[(0, 0, "")]

-- Single line without newline.
#guard lineInfoData "hello" = #[(5, 0, "hello")]

-- Leading spaces count toward both length and indentation.
#guard lineInfoData "  hello" = #[(7, 2, "  hello")]

-- Multiple lines split at '\n'.
#guard lineInfoData "hello\nworld" = #[(5, 0, "hello"), (5, 0, "world")]

-- Trailing '\n' produces an empty last line.
#guard lineInfoData "abc\n" = #[(3, 0, "abc"), (0, 0, "")]

-- Line of only spaces: indentation equals length.
#guard lineInfoData "   " = #[(3, 3, "   ")]

-- Spaces after a non-space character don't count toward indentation.
#guard lineInfoData "  ab cd" = #[(7, 2, "  ab cd")]

-- Trailing spaces count toward length but not indentation.
#guard lineInfoData "hello  " = #[(7, 0, "hello  ")]

-- Multiple consecutive newlines produce empty intermediate lines.
#guard lineInfoData "\n\n" = #[(0, 0, ""), (0, 0, ""), (0, 0, "")]

-- Two indented lines.
#guard lineInfoData "  hello\n  world" = #[(7, 2, "  hello"), (7, 2, "  world")]

-- Three lines, the middle one empty.
#guard lineInfoData "a\n\nb" = #[(1, 0, "a"), (0, 0, ""), (1, 0, "b")]

-- ===== collectSyntaxLineInfos =====
-- Assumption: leading is always empty, Syntax.node has no SourceInfo.

-- .missing produces a single empty line at position 0.
#guard syntaxLineInfoData .missing = #[(0, 0, "", 0, 0)]

-- Single atom with SourceInfo.none: byte positions track the atom value.
#guard syntaxLineInfoData (.atom .none "hello") = #[(5, 0, "hello", 0, 5)]

-- Indented atom: leading spaces of a token value do not count toward indentation.
#guard syntaxLineInfoData (.atom .none "  hello") = #[(7, 0, "  hello", 0, 7)]

-- Empty atom is a no-op.
#guard syntaxLineInfoData (.atom .none "") = #[(0, 0, "", 0, 0)]

-- Ident node uses rawVal.toString.
#guard syntaxLineInfoData (.ident .none "hello".toRawSubstring `hello []) = #[(5, 0, "hello", 0, 5)]

-- Node with two adjacent atoms: contents are merged on the same pending line.
#guard syntaxLineInfoData (.node .none `null #[.atom .none "a", .atom .none "b"])
  = #[(2, 0, "ab", 0, 2)]

-- Atom with trailing space extends the pending line.
-- "hello " occupies bytes [0, 6).
#guard syntaxLineInfoData (mkAtomTrailing "hello" " ") = #[(6, 0, "hello ", 0, 6)]

-- Trailing containing a newline splits into two lines.
-- Source: "hello" (bytes [0,5)) + " \n" (bytes [5,7)) + "world" (bytes [7,12))
-- Line 1: "hello " occupies bytes [0, 6) (the '\n' is at byte 6).
-- Line 2: "world" occupies bytes [7, 12).
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "hello" " \n",
    .atom .none "world"
  ]) = #[(6, 0, "hello ", 0, 6), (5, 0, "world", 7, 12)]

-- The indentation of the second line is accumulated from the trailing of the first atom.
-- Source: "  hello" (bytes [0,7)) + "\n  " (bytes [7,10)) + "world" (bytes [10,15))
-- Line 1: "  hello" (the leading spaces are part of the token value), startPos=0, endPos=7.
-- Line 2: "  world" (indentation "  " from trailing + "world"), startPos=8, endPos=15.
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "  hello" "\n  ",
    .atom .none "world"
  ]) = #[(7, 0, "  hello", 0, 7), (7, 2, "  world", 8, 15)]

-- Three tokens across two lines: "a b" + "\n" + "c"
-- "a" = byte [0,1), " b" (trailing of a) -> combined "a b" at [0,3), '\n' at byte 3,
-- "c" = bytes [4,5).
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "a" " b\n",
    .atom .none "c"
  ]) = #[(3, 0, "a b", 0, 3), (1, 0, "c", 4, 5)]

-- When the pending line is all spaces (from trailing) and the next atom starts with spaces,
-- only the spaces from the trailing count toward indentation.
-- Source: "" (atom) + "\n  " (trailing, bytes [0,3)) + "  hello" (atom, bytes [3,10))
--   '\n' is byte 0; "  " (indentation) spans bytes [1,3); "  hello" spans bytes [3,10).
-- Line 1: "" (before '\n'), length=0, indentation=0, startPos=0, endPos=0.
-- Line 2: "    hello" (merged "  " + "  hello"), length=9, indentation=2, startPos=1, endPos=10.
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "" "\n  ",
    .atom .none "  hello"
  ]) = #[(0, 0, "", 0, 0), (9, 2, "    hello", 1, 10)]

-- ===== collectSyntaxLineInfos token ranges =====
-- Every line reports the full range of each token it is covered by, so a multi-line token is
-- reported unchanged on every one of its lines.

-- .missing contributes no tokens.
#guard syntaxLineTokenData .missing = #[#[]]

-- A single atom is a token spanning its whole value.
#guard syntaxLineTokenData (.atom .none "hello") = #[#[(0, 5)]]

-- An empty atom is still a token, albeit an empty one.
#guard syntaxLineTokenData (.atom .none "") = #[#[(0, 0)]]

-- Idents are tokens too.
#guard syntaxLineTokenData (.ident .none "hello".toRawSubstring `hello []) = #[#[(0, 5)]]

-- Adjacent atoms produce two tokens on the same line.
#guard syntaxLineTokenData (.node .none `null #[.atom .none "a", .atom .none "b"])
  = #[#[(0, 1), (1, 2)]]

-- Trailing whitespace is not part of the token.
#guard syntaxLineTokenData (mkAtomTrailing "hello" " ") = #[#[(0, 5)]]

-- Whitespace-only advances contribute no tokens.
-- Source: "hello" (bytes [0,5)) + " \n" (bytes [5,7)) + "world" (bytes [7,12))
#guard syntaxLineTokenData (.node .none `null #[
    mkAtomTrailing "hello" " \n",
    .atom .none "world"
  ]) = #[#[(0, 5)], #[(7, 12)]]

-- A token spanning two lines is reported with its full range on both of them.
-- Source: "a" [0,1) + '\n' at byte 1 + "b" [2,3); the token spans [0,3).
#guard syntaxLineTokenData (.atom .none "a\nb") = #[#[(0, 3)], #[(0, 3)]]

-- Likewise for a line that is fully covered by a token.
-- Source: "a" [0,1) + "b" [2,3) + "c" [4,5); the token spans [0,5).
#guard syntaxLineTokenData (.atom .none "a\nb\nc") = #[#[(0, 5)], #[(0, 5)], #[(0, 5)]]

-- A line ending in a multi-line token reports both that token and the one following it.
-- Source: "a\nb" [0,3) + "c" [3,4).
#guard syntaxLineTokenData (.node .none `null #[.atom .none "a\nb", .atom .none "c"])
  = #[#[(0, 3)], #[(0, 3), (3, 4)]]

-- A token ending in a newline also covers the empty line after it.
-- Source: "a" [0,1) + '\n' at byte 1; the token spans [0,2).
#guard syntaxLineTokenData (.atom .none "a\n") = #[#[(0, 2)], #[(0, 2)]]

-- ===== collectSyntaxLineInfos' =====

-- Extracts (length, indentation, line, startPos.byteIdx, endPos.byteIdx) for each line.
-- Lines that start within a token are reported with indentation 0.
def syntaxLineInfoData' (source : String) (stx : Lean.Syntax) :
    Array (Nat × Nat × String × Nat × Nat) :=
  (collectSyntaxLineInfos' source.toSlice stx).map fun info =>
    (info.length, info.indentation, info.line, info.startPos.byteIdx, info.endPos.byteIdx)

-- Extracts (start.byteIdx, stop.byteIdx) of every token range of every line.
def syntaxLineTokenData' (source : String) (stx : Lean.Syntax) :
    Array (Array (Nat × Nat)) :=
  (collectSyntaxLineInfos' source.toSlice stx).map fun info =>
    info.tokenRanges.map fun range => (range.start.byteIdx, range.stop.byteIdx)

-- Constructs an atom whose value and whitespace are substrings of `source`:
-- leading is [leadingStartPos, pos), the value is [pos, tailPos) and
-- trailing is [tailPos, trailingStopPos).
private def mkSourceAtom (source : String) (leadingStartPos pos tailPos trailingStopPos : Nat) :
    Lean.Syntax :=
  let val : Substring.Raw := ⟨source, ⟨pos⟩, ⟨tailPos⟩⟩
  .atom
    (.original ⟨source, ⟨leadingStartPos⟩, ⟨pos⟩⟩ ⟨pos⟩ ⟨source, ⟨tailPos⟩, ⟨trailingStopPos⟩⟩
      ⟨tailPos⟩)
    val.toString

-- Empty source with missing syntax: one empty line.
#guard syntaxLineInfoData' "" .missing = #[(0, 0, "", 0, 0)]

-- Two lines of single-line tokens: line information matches `collectLineInfos`,
-- no line starts in a token.
-- Source: "ab" [0,2) + " " + "cd" [3,5) + "\n" + "ef" [6,8).
#guard syntaxLineInfoData' "ab cd\nef" (.node .none `null #[
    mkSourceAtom "ab cd\nef" 0 0 2 3,
    mkSourceAtom "ab cd\nef" 3 3 5 6,
    mkSourceAtom "ab cd\nef" 6 6 8 8
  ]) = #[(5, 0, "ab cd", 0, 5), (2, 0, "ef", 6, 8)]

-- Indentation of lines that start in whitespace is preserved.
-- Source: "a" [0,1) + "\n  " (trailing, bytes [1,4)) + "b" [4,5).
#guard syntaxLineInfoData' "a\n  b" (.node .none `null #[
    mkSourceAtom "a\n  b" 0 0 1 4,
    mkSourceAtom "a\n  b" 4 4 5 5
  ]) = #[(1, 0, "a", 0, 1), (3, 2, "  b", 2, 5)]

-- A line starting within a multi-line token starts in a token and has indentation 0.
-- Source: "k" [0,1) + " " + "\"a\nb\"" [2,7) + " " (trailing, byte 7) + "m" [8,9).
#guard syntaxLineInfoData' "k \"a\nb\" m" (.node .none `null #[
    mkSourceAtom "k \"a\nb\" m" 0 0 1 2,
    mkSourceAtom "k \"a\nb\" m" 2 2 7 8,
    mkSourceAtom "k \"a\nb\" m" 8 8 9 9
  ]) = #[(4, 0, "k \"a", 0, 4), (4, 0, "b\" m", 5, 9)]

-- A line starting exactly at the start of a multi-line token does not start in the token,
-- but the line starting within it does.
-- Source: "a" [0,1) + "\n" (trailing, byte 1) + "\"b\nc\"" [2,7).
#guard syntaxLineInfoData' "a\n\"b\nc\"" (.node .none `null #[
    mkSourceAtom "a\n\"b\nc\"" 0 0 1 2,
    mkSourceAtom "a\n\"b\nc\"" 2 2 7 7
  ]) = #[(1, 0, "a", 0, 1), (2, 0, "\"b", 2, 4), (2, 0, "c\"", 5, 7)]

-- Lines starting in the region of a token without source positions are assumed to start in a
-- token, so their indentation is reported as 0 instead of 2.
-- Source: "a" [0,1) + " " (trailing, byte 1) + "/-- doc\n  text -/" (broken token, bytes [2,19))
-- + " " (leading of "b", byte 19) + "b" [20,21).
#guard syntaxLineInfoData' "a /-- doc\n  text -/ b" (.node .none `null #[
    mkSourceAtom "a /-- doc\n  text -/ b" 0 0 1 2,
    .atom .none "/-- doc\n  text -/",
    mkSourceAtom "a /-- doc\n  text -/ b" 19 20 21 21
  ]) = #[(9, 0, "a /-- doc", 0, 9), (11, 0, "  text -/ b", 10, 21)]

-- A line starting exactly at the start of a region of a token without source positions is
-- assumed to start in a token, unlike for tokens with source positions.
-- Source: "a" [0,1) + "\n" (trailing, byte 1) + "BROKEN" (broken token, bytes [2,8))
-- + "\n" (leading of "b", byte 8) + "b" [9,10).
#guard syntaxLineInfoData' "a\nBROKEN\nb" (.node .none `null #[
    mkSourceAtom "a\nBROKEN\nb" 0 0 1 2,
    .atom .none "BROKEN",
    mkSourceAtom "a\nBROKEN\nb" 8 9 10 10
  ]) = #[(1, 0, "a", 0, 1), (6, 0, "BROKEN", 2, 8), (1, 0, "b", 9, 10)]

-- A region of a token without source positions at the end of the source extends to the end of
-- the source.
-- Source: "a" [0,1) + "\n" (trailing, byte 1) + "BROKEN end" (broken token, bytes [2,12)).
#guard syntaxLineInfoData' "a\nBROKEN end" (.node .none `null #[
    mkSourceAtom "a\nBROKEN end" 0 0 1 2,
    .atom .none "BROKEN end"
  ]) = #[(1, 0, "a", 0, 1), (10, 0, "BROKEN end", 2, 12)]

-- A source consisting only of a token without source positions: all lines are assumed to start
-- in a token, so the indentation of the second line is reported as 0 instead of 2.
#guard syntaxLineInfoData' "BROKEN\n  BROKEN" (.atom .none "BROKEN\n  BROKEN")
  = #[(6, 0, "BROKEN", 0, 6), (8, 0, "  BROKEN", 7, 15)]

-- ===== collectSyntaxLineInfos' token ranges =====

-- Empty source with missing syntax: no tokens.
#guard syntaxLineTokenData' "" .missing = #[#[]]

-- Every token of a line is reported, whitespace is not part of any token.
-- Source: "ab" [0,2) + " " + "cd" [3,5) + "\n" + "ef" [6,8).
#guard syntaxLineTokenData' "ab cd\nef" (.node .none `null #[
    mkSourceAtom "ab cd\nef" 0 0 2 3,
    mkSourceAtom "ab cd\nef" 3 3 5 6,
    mkSourceAtom "ab cd\nef" 6 6 8 8
  ]) = #[#[(0, 2), (3, 5)], #[(6, 8)]]

-- Leading whitespace of a line is not part of the token that follows it.
-- Source: "a" [0,1) + "\n  " (trailing, bytes [1,4)) + "b" [4,5).
#guard syntaxLineTokenData' "a\n  b" (.node .none `null #[
    mkSourceAtom "a\n  b" 0 0 1 4,
    mkSourceAtom "a\n  b" 4 4 5 5
  ]) = #[#[(0, 1)], #[(4, 5)]]

-- A multi-line token is reported with its full range on every line it covers.
-- Source: "k" [0,1) + " " + "\"a\nb\"" [2,7) + " " (trailing, byte 7) + "m" [8,9).
#guard syntaxLineTokenData' "k \"a\nb\" m" (.node .none `null #[
    mkSourceAtom "k \"a\nb\" m" 0 0 1 2,
    mkSourceAtom "k \"a\nb\" m" 2 2 7 8,
    mkSourceAtom "k \"a\nb\" m" 8 8 9 9
  ]) = #[#[(0, 1), (2, 7)], #[(2, 7), (8, 9)]]

-- Lines fully covered by a token report just that token.
-- Source: "a" [0,1) + "\n" (trailing, byte 1) + "\"b\nc\nd\"" [2,9).
#guard syntaxLineTokenData' "a\n\"b\nc\nd\"" (.node .none `null #[
    mkSourceAtom "a\n\"b\nc\nd\"" 0 0 1 2,
    mkSourceAtom "a\n\"b\nc\nd\"" 2 2 9 9
  ]) = #[#[(0, 1)], #[(2, 9)], #[(2, 9)], #[(2, 9)]]

-- The region of a token without source positions is conservatively reported as a single token.
-- Source: "a" [0,1) + " " (trailing, byte 1) + "/-- doc\n  text -/" (broken token, bytes [2,19))
-- + " " (leading of "b", byte 19) + "b" [20,21).
#guard syntaxLineTokenData' "a /-- doc\n  text -/ b" (.node .none `null #[
    mkSourceAtom "a /-- doc\n  text -/ b" 0 0 1 2,
    .atom .none "/-- doc\n  text -/",
    mkSourceAtom "a /-- doc\n  text -/ b" 19 20 21 21
  ]) = #[#[(0, 1), (2, 19)], #[(2, 19), (20, 21)]]

-- A region of a token without source positions at the end of the source extends to the end of
-- the source.
-- Source: "a" [0,1) + "\n" (trailing, byte 1) + "BROKEN end" (broken token, bytes [2,12)).
#guard syntaxLineTokenData' "a\nBROKEN end" (.node .none `null #[
    mkSourceAtom "a\nBROKEN end" 0 0 1 2,
    .atom .none "BROKEN end"
  ]) = #[#[(0, 1)], #[(2, 12)]]

-- A source consisting only of a token without source positions is one region spanning all lines.
#guard syntaxLineTokenData' "BROKEN\n  BROKEN" (.atom .none "BROKEN\n  BROKEN")
  = #[#[(0, 15)], #[(0, 15)]]
