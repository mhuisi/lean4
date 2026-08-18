import Std.Tactic.BVDecide

/-!
Tests for the formatters of the `bv_decide` family of tactics: `bv_decide`, `bv_decide?`,
`bv_check` and `bv_normalize` (`fmtBvDecide`, `fmtBvTrace`, `fmtBvCheck`, `fmtBvNormalize`),
their `grind =>`/`sym =>` mode counterparts together with `bv_decide_push` and `lift_lets`
(`fmtGrindBvDecide`, `fmtGrindBvTrace`, `fmtGrindBvCheck`, `fmtGrindBvNormalize`,
`fmtGrindBvDecidePush`), and the `types [...]` clause that they share (`fmtBvTypes`). Every
section contains forms that fit on one line, forms that exceed the 100 column soft width, and
forms with and without each optional component.
-/

inductive Channel where
  | red
  | green
  | blue

inductive BlendMode where
  | normal
  | multiply
  | screen

structure Pixel where
  luminance : BitVec 8
  alpha : BitVec 8

structure Sample where
  left : BitVec 8
  right : BitVec 8

structure ColorRamp where
  start : BitVec 8
  stop : BitVec 8

structure ToneCurve where
  gain : BitVec 8
  bias : BitVec 8

section BvDecide

example (x y : BitVec 8) : x + y = y + x := by
  bv_decide

example (x y : BitVec 8) : x &&& y = y &&& x := by
  bv_decide (timeout := 1)

example (x y : BitVec 8) : x ||| y = y ||| x := by
  bv_decide +acNf -structures (timeout := 1)

example (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  bv_decide +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 1)

example (a b : Pixel) (h : a = b) : a.luminance = b.luminance := by
  bv_decide types [Pixel]

example (c d : Channel) (h : c = d) : d = c := by
  bv_decide +acNf types [Channel]

example (a b : Pixel) (c d : Channel) (h₁ : a = b) (h₂ : c = d) :
    a.alpha = b.alpha ∧ d = c := by
  bv_decide (timeout := 1) types [Pixel, Channel]

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  bv_decide types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  bv_decide +acNf +shortCircuit -fixedInt (maxSteps := 100000) (timeout := 1)
    types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

end BvDecide

section BvTrace

example (x y : BitVec 8) : x + y = y + x := by
  bv_decide?

example (x y z : BitVec 8) : x + (y + z) = (y + z) + x := by
  bv_decide? +acNf -embeddedConstraintSubst (timeout := 1)

example (a b : Pixel) (h : a = b) : a.luminance = b.luminance := by
  bv_decide? types [Pixel]

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  bv_decide? +acNf -structures (timeout := 1)
    types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

end BvTrace

section BvCheck

example (x y : BitVec 8) : x + y = y + x := by
  bv_check "bv_add_comm.lrat"

example (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  bv_check +acNf -structures (timeout := 1) "bv_xor_comm.lrat"

example (a b : Pixel) (h : a = b) : a.luminance = b.luminance := by
  bv_check types [Pixel] "pixel_luminance.lrat"

example (x y : BitVec 8) : x * y = y * x := by
  bv_check +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 1)
    "bv_mul_comm.lrat"

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  bv_check +acNf (timeout := 1)
    types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]
    "pixel_sample_alpha.lrat"

end BvCheck

section BvNormalize

example (x y : BitVec 8) : x + y = y + x := by
  bv_normalize

example (x y : BitVec 8) : x + y = y + x := by
  bv_normalize +acNf

example (x y : BitVec 8) : x &&& y = y &&& x := by
  bv_normalize (maxSteps := 10000)

example (a b : Pixel) (h : a = b) : a.luminance = b.luminance := by
  bv_normalize types [Pixel]

example (x y : BitVec 8) : x ^^^ y = y ^^^ x := by
  bv_normalize +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 120)

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  bv_normalize +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000) (timeout := 120)
    types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

@[bv_normalize]
theorem BitVec.and_self_left' (x y : BitVec w) : x &&& (x &&& y) = x &&& y := sorry

end BvNormalize

section GrindMode

example (x y : BitVec 8) : x + y = y + x := by
  grind =>
    bv_decide

example (x y : BitVec 8) : x + y = y + x := by
  sym =>
    lift_lets
    bv_normalize +acNf

example (a b : Pixel) (h : a = b) : a.luminance = b.luminance := by
  grind =>
    bv_decide types [Pixel]

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  sym =>
    bv_decide +acNf -structures (timeout := 1)
      types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

example (x y : BitVec 8) : x + y = y + x := by
  grind =>
    bv_decide?

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  sym =>
    bv_decide? (timeout := 1)
      types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]

example (x y : BitVec 8) : x + y = y + x := by
  grind =>
    bv_check "bv_add_comm.lrat"

example (a b : Pixel) (s t : Sample) (h₁ : a = b) (h₂ : s = t) :
    a.alpha = b.alpha ∧ s.left = t.left := by
  sym =>
    bv_check +acNf (timeout := 1)
      types [Pixel, Sample, Channel, BlendMode, ColorRamp, ToneCurve, Pixel, Sample]
      "pixel_sample_alpha.lrat"

example (x y : BitVec 8) : x + y = y + x := by
  sym =>
    bv_decide_push
    bv_decide

example (x y : BitVec 8) : x + y = y + x := by
  grind =>
    bv_decide_push +acNf +shortCircuit -structures -fixedInt -enums (maxSteps := 100000)
    bv_decide

end GrindMode
