import Std.Time

/-!
Tests for the formatters of the subarray slice notations `a[i:j]`, `a[i:]` and `a[:j]`
(`fmtSubarrayBounds`, `fmtSubarrayLowerBound`, `fmtSubarrayUpperBound`), of the legacy range
literals `[i:j]`, `[:j]`, `[:j:k]` and `[i:j:k]` (`fmtLegacyRangeBounds`,
`fmtLegacyRangeUpperBound`, `fmtLegacyRangeUpperBoundWithStep`, `fmtLegacyRangeBoundsWithStep`),
of the `Std.Time` notations `zoned(...)`, `datetime(...)`, `date(...)`, `time(...)`,
`offset(...)` and `timezone(...)` (`fmtZonedDateTime`, `fmtZonedDateTimeWithTimeZone`,
`fmtPlainDateTime`, `fmtPlainDate`, `fmtPlainTime`, `fmtTimeZoneOffset`, `fmtTimeZone`), of
`satisfies_binder_pred%` (`fmtSatisfiesBinderPred`), of `Macro.trace[...]` (`fmtMacroTrace`) and
of `println!` (`fmtPrintln`). Every section contains forms that fit on one line, forms that
exceed the 100 column soft width, and forms with and without each optional component.
-/

def numberOfWarmupSamples : Nat := 32
def numberOfCooldownSamples : Nat := 16

section SubarraySlices

def firstHalf (xs : Array Nat) : Subarray Nat :=
  xs[0 : xs.size / 2]

def secondHalf (xs : Array Nat) : Subarray Nat :=
  xs[xs.size / 2 :]

def upTo (xs : Array Nat) (bound : Nat) : Subarray Nat :=
  xs[: min bound xs.size]

def steadyState (measurements : Array Float) : Subarray Float :=
  measurements[numberOfWarmupSamples : measurements.size - numberOfCooldownSamples]

def steadyStateOfNamedBenchmark (measurements : Array Float) (benchmarkName : String) : Subarray Float :=
  measurements[numberOfWarmupSamples + benchmarkName.length : measurements.size - numberOfCooldownSamples - benchmarkName.length]

def tailAfterWarmup (measurements : Array Float) (additionalSamplesToDiscardBeforeMeasuring : Nat) : Subarray Float :=
  measurements[numberOfWarmupSamples + additionalSamplesToDiscardBeforeMeasuring + measurements.size / 100 :]

def headBeforeCooldown (measurements : Array Float) (additionalSamplesToDiscardAfterMeasuring : Nat) : Subarray Float :=
  measurements[: measurements.size - numberOfCooldownSamples - additionalSamplesToDiscardAfterMeasuring - 1]

def innerSliceOfInnerSlice (xs : Array Nat) : Subarray Nat :=
  xs[1 : xs.size - 1].toArray[1 : xs.size - 2]

def sumOfSteadyState (measurements : Array Float) : Float :=
  measurements[numberOfWarmupSamples : measurements.size - numberOfCooldownSamples].foldl (· + ·) (0 : Float)

end SubarraySlices

section LegacyRanges

def sumUpTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [:n] do
    acc := acc + i
  return acc

def sumBetween (lo hi : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [lo:hi] do
    acc := acc + i
  return acc

def sumEveryOtherUpTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [:n:2] do
    acc := acc + i
  return acc

def sumEveryOtherBetween (lo hi : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [lo:hi:2] do
    acc := acc + i
  return acc

def steadyStateIndices (measurements : Array Float) : Std.Legacy.Range :=
  [numberOfWarmupSamples : measurements.size - numberOfCooldownSamples]

def sumOfEverySecondSteadyStateMeasurement (measurements : Array Float) : Float := Id.run do
  let mut acc := (0 : Float)
  for i in [numberOfWarmupSamples : measurements.size - numberOfCooldownSamples - numberOfWarmupSamples : 2] do
    acc := acc + measurements[i]!
  return acc

def sumOfEveryFourthLeadingMeasurement (measurements : Array Float) : Float := Id.run do
  let mut acc := (0 : Float)
  for i in [: measurements.size - numberOfCooldownSamples - numberOfWarmupSamples - measurements.size / 100 : 4] do
    acc := acc + measurements[i]!
  return acc

end LegacyRanges

section TimeNotations

open Std.Time

def brasiliaOffset : TimeZone.Offset :=
  offset("-03:00")

def brasilia : TimeZone :=
  timezone("America/Sao_Paulo -03:00")

def meetingStart :=
  zoned("2024-10-13T15:00:00-03:00")

def meetingStartInBrasilia :=
  zoned("2024-10-13T15:00:00", TimeZone.ZoneRules.ofTimeZone brasilia)

def releaseTimestamp : PlainDateTime :=
  datetime("2024-10-13T15:00:00")

def releaseDate : PlainDate :=
  date("2024-10-13")

def dailyStandup : PlainTime :=
  time("09:30:00")

def conferenceOpening :=
  zoned("2024-10-13T15:00:00", .ofTimeZone (TimeZone.mk brasiliaOffset "America/Sao_Paulo" "BRT" false))

def conferenceClosingInTheTimeZoneOfTheVenue :=
  zoned("2024-10-17T18:45:00", .ofTimeZone (TimeZone.mk brasiliaOffset "America/Sao_Paulo" "Brasilia Standard Time" false))

def scheduleOfTheFirstConferenceDay : List (PlainTime × String) :=
  [(time("09:00:00"), "registration"), (time("10:00:00"), "keynote"), (time("12:30:00"), "lunch")]

end TimeNotations

section SatisfiesBinderPred

example (n : Nat) : Prop := satisfies_binder_pred% n > 0

example (n : Nat) : Prop := satisfies_binder_pred% n ≤ 128

example (xs : List Nat) (x : Nat) : Prop := satisfies_binder_pred% x ∈ xs

example (xs ys : List Nat) : Prop := satisfies_binder_pred% xs ⊆ ys

example (measurements : Array Float) (i : Nat) : Prop :=
  satisfies_binder_pred% i < measurements.size - numberOfCooldownSamples - numberOfWarmupSamples

example (measurements : Array Float) (indicesOfDiscardedSamples : List Nat) : Prop :=
  satisfies_binder_pred% (numberOfWarmupSamples + measurements.size) ∉ indicesOfDiscardedSamples.map (· + numberOfCooldownSamples)

end SatisfiesBinderPred

section MacroTrace

open Lean

macro "default_warmup" : term => do
  Macro.trace[Elab.definition] "using the default warmup"
  `(numberOfWarmupSamples)

macro "warmup_of " name:str : term => do
  Macro.trace[Elab.definition.body] "using the warmup configured for {name.getString}"
  `(numberOfWarmupSamples)

macro "benchmark_schedule " name:str " at " start:str : term => do
  Macro.trace[Elab.definition.body.imperative] "scheduling the benchmark {name.getString} to start at {start.getString} after discarding the warmup samples"
  `(($start, $name))

end MacroTrace

section Println

def reportSteadyState (measurements : Array Float) : IO Unit := do
  println! "steady state"
  println! measurements.size
  println! s!"{measurements.size} measurements"
  println! "discarded {numberOfWarmupSamples} warmup and {numberOfCooldownSamples} cooldown samples"
  println! "the steady state of the benchmark consists of {measurements.size - numberOfWarmupSamples - numberOfCooldownSamples} samples"
  println! measurements[numberOfWarmupSamples : measurements.size - numberOfCooldownSamples].foldl (· + ·) (0 : Float)

end Println
