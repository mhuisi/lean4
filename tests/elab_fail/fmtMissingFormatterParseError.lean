/-!
Tests that the `missingFormatter` linter skips commands with parse errors: the `missing` nodes left
behind by parser error recovery make formatters fail, which would be reported as spurious incomplete
formatters. `showPartialSyntaxErrors` is what makes linter output on such commands visible at all.
-/

set_option linter.missingFormatter true
set_option showPartialSyntaxErrors true

def g (x : Nat) : Nat := x +
