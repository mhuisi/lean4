structure S :=
(x : Nat) (y : Bool) (z : Nat) (w : Nat)

set_option trace.compiler.stage1 true

def g : S → S
| s@{ x := x, ..} => { s with x := x + 1 }
