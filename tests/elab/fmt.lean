import Lean.Fmt.Core.Formatter

/-!
Tests the renderings chosen by the core of the auto-formatter for various documents.
-/

open Lean.Fmt

-- Optimality cutoff width used by all tests in this file.
abbrev cutoff := 200

def traditional : Doc τ :=
  .join #[
    .text "function append(first,second,third){",
    .indented 4 true (
      let f : Doc τ := .text "first +"
      let s : Doc τ := .text "second +"
      let t : Doc τ := .text "third"
      .join #[
        .nl,
        .text "return ",
        .maybeFlattened (.indented 4 true (.join #[f, .nl, s, .nl, t]))]
    ),
    .nl,
    .text "}"
  ]

def test (width : Nat) (d : Doc (DefaultCost width cutoff)) (pre : String := "") : IO Unit := do
  IO.println ""
  let r? := format? width cutoff d (taintedResolution := true) (offset := pre.length)
  IO.println (pre ++ (r?.toOption.map (·.rendering) |>.getD ""))

/--
info:
function append(first,second,third){
    return first +
        second +
        third
}
-/
#guard_msgs in
#eval test 22 traditional

/--
info:
function append(first,second,third){
    return first + second + third
}
-/
#guard_msgs in
#eval test 36 traditional

inductive SExpr where
  | leaf (v : String)
  | node (cs : List SExpr)

instance : Coe String SExpr where
  coe v := .leaf v

partial def SExpr.pretty (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty
    let argsp := args.toArray.map pretty
    .oneOf #[
      .join #[
        .text "(",
        .aligned (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned fp,
        .text " ",
        .aligned (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .flattened (
        .join #[
          .text "(",
          .aligned (.joinUsing (.text " ") (#[fp] ++ argsp)),
          .text ")"
        ]
      )
    ]

partial def SExpr.pretty' (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty'
    let argsp := args.toArray.map pretty'
    .oneOf #[
      .join #[
        .text "(",
        .aligned (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned fp,
        .text " ",
        .aligned (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned (.joinUsing (.text " ") (#[fp] ++ argsp)),
        .text ")"
      ]
    ]

partial def SExpr.pretty'' (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty''
    let argsp := args.toArray.map pretty''
    .oneOf #[
      .join #[
        .text "(",
        .nested (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .flattened (
        .join #[
          .text "(",
          .nested (.joinUsing (.text " ") (#[fp] ++ argsp)),
          .text ")"
        ]
      )
    ]

def testSExpr (width : Nat) (e : SExpr) (pre : String := "") : IO Unit := do
  test width e.pretty pre

def testSExpr' (width : Nat) (e : SExpr) : IO Unit := do
  test width e.pretty'

def testSExpr'' (width : Nat) (e : SExpr) (pre : String := "") : IO Unit := do
  test width e.pretty'' pre

def sExpr1 : SExpr :=
  .node ["+", .node ["foo", "1", "2"], .node ["bar", "2", "3"], .node ["baz", "3", "4"]]

/--
info:
(+ (foo 1 2)
   (bar 2 3)
   (baz 3 4))
-/
#guard_msgs in
#eval testSExpr 31 sExpr1

/--
info:
(+ (foo 1 2) (bar 2 3) (baz 3
                            4))
-/
#guard_msgs in
#eval testSExpr' 31 sExpr1

def sExpr2 : SExpr := .node ["+", "123", "456", "789"]


/--
info:
(+ 123 456 789)
-/
#guard_msgs in
#eval testSExpr 15 sExpr2

/--
info:
(+ 123
   456
   789)
-/
#guard_msgs in
#eval testSExpr 14 sExpr2

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr 5 sExpr2

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr 0 sExpr2

def sExpr3 : SExpr :=
  .node ["a", "b", "c", "d"]

def sExpr4 : SExpr :=
  .node [sExpr3, sExpr3, sExpr3, sExpr3]

def sExpr5 : SExpr :=
  .node [.node ["abcde", sExpr4], .node ["abcdefgh", sExpr4]]

def pre1 := "hello: "

/--
info:
hello: ((abcde ((a b c d)
                (a b c d)
                (a b c d)
                (a b c d)))
        (abcdefgh
         ((a b c d)
          (a b c d)
          (a b c d)
          (a b c d))))
-/
#guard_msgs in
#eval testSExpr (20 + pre1.length) sExpr5 pre1

/--
info:
hello: ((abcde
  ((a b c d)
    (a b c d)
    (a b c d)
    (a b c d)))
  (abcdefgh
    ((a b c d)
      (a b c d)
      (a b c d)
      (a b c d))))
-/
#guard_msgs in
#eval testSExpr'' (20 + pre1.length) sExpr5 pre1

/--
info:
abc
def
-/
#guard_msgs in
#eval test 80
  (.indented 4 true (.unindented false (.joinUsing .hardNl #[.text "abc", .text "def"])))

/--
info:
abc
    def
-/
#guard_msgs in
#eval test 80 (.indented 4 true (.joinUsing .hardNl #[.text "abc", .text "def"]))

/--
info:
something
-/
#guard_msgs in
#eval test 80 (.either (.joinUsing .hardNl #[.text "abc", .text "def"]) (.text "something"))

/-- info: none -/
#guard_msgs in
#eval format? 80 cutoff .failure (taintedResolution := true) |>.toOption.map (·.rendering)

def concated (n : Nat) : Doc τ :=
  if n = 0 then
    .text ""
  else
    .append (concated (n - 1)) (.text "line")

/--
info:
linelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelineline
-/
#guard_msgs in
#eval test 100 (concated 100)
