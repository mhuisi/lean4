import Lean.Meta
open Lean
open Lean.Meta

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throw $ Exception.other "check failed"

def nat   := mkConst `Nat
def boolE := mkConst `Bool
def succ  := mkConst `Nat.succ
def zero  := mkConst `Nat.zero
def add   := mkConst `Nat.add
def io    := mkConst `IO
def type  := mkSort levelOne
def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def tst1 : MetaM Unit := do
print "----- tst1 -----";
m1 ← mkFreshExprMVar (mkArrow nat nat);
let lhs := mkApp m1 zero;
let rhs := zero;
check $ fullApproxDefEq $ isDefEq lhs rhs;
pure ()

set_option pp.all true
set_option trace.Meta.isDefEq true

#eval tst1

set_option trace.Meta true
set_option trace.Meta.isDefEq false

def tst2 : MetaM Unit := do
print "----- tst2 -----";
ps ← getParamNames `Or.elim; print (toString ps);
ps ← getParamNames `Iff.elim; print (toString ps);
ps ← getParamNames `check; print (toString ps);
pure ()

#eval tst2

axiom t1 : [Unit] = []
axiom t2 : 0 > 5

def tst3 : MetaM Unit := do
env ← getEnv;
t2  ← getConstInfo `t2;
c   ← mkNoConfusion t2.type (mkConst `t1);
print c;
Meta.check c;
cType ← inferType c;
print cType;
pure ()

set_option pp.all true
#eval tst3
