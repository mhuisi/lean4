/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.ToString.Macro
import Init.Data.String.Basic

public section

namespace Std
namespace Internal
namespace Parsec

/--
Represents an error that can occur during parsing.
-/
inductive Error where
  /--
  Indicates that the parser reached the end of the input unexpectedly.
  -/
  | eof

  /--
  Represents any other kind of parsing error with an associated message.
  -/
  | other (s : String)
deriving Repr

instance : ToString Error where
  toString
    | .eof => "unexpected end of input"
    | .other s => s

/--
The result of parsing some string.
-/
inductive ParseResult (α : Type) (ι : Type) where
  /--
  Parsing succeeded, returning the new position `pos` and the parsed result `res`.
  -/
  | success (pos : ι) (res : α)

  /--
  Parsing failed, returning the position `pos` where the error occurred and the error `err`.
  -/
  | error (pos : ι) (err : Error)
deriving Repr

end Parsec

/--
A `ParsecT ι m α` represents a parser that consumes input of type `ι` and, produces a
`ParseResult` containing a value of type `α` (the result of parsing) and the remaining input.
-/
@[expose]
def ParsecT (ι : Type) (m : Type → Type) (α : Type) : Type :=
  ι → m (Parsec.ParseResult α ι)

@[expose]
abbrev Parsec (ι : Type) (α : Type) : Type := ParsecT ι Id α

namespace Parsec

/--
Interface for an input iterator with position tracking and lookahead support.
-/
class Input (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι → idx
  next : ι → ι
  curr : ι → elem
  hasNext : ι → Bool
  next' (it : ι) : (hasNext it) → ι
  curr' (it : ι) : (hasNext it) → elem

variable {m : Type → Type} [Monad m]
variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Input ι elem idx]

@[always_inline, inline]
protected def pure (a : α) : ParsecT ι m α := fun it =>
  pure <| .success it a

@[always_inline, inline]
protected def bind {α β : Type} (f : ParsecT ι m α) (g : α → ParsecT ι m β) : ParsecT ι m β := fun it => do
  match ← f it with
  | .success rem a => g a rem
  | .error pos msg => pure <| .error pos msg

/--
Parser that always fails with the given error message.
-/
@[always_inline, inline]
def fail (msg : String) : ParsecT ι m α := fun it =>
  pure <| .error it (.other msg)

/--
Try `p`, then decide what to do based on success or failure without consuming input on failure.
-/
@[inline]
def tryCatch (p : ParsecT ι m α) (csuccess : α → ParsecT ι m β) (cerror : Unit → ParsecT ι m β)
    : ParsecT ι m β := fun it => do
  match ← p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if Input.pos it = Input.pos rem then cerror () rem else pure <| .error rem err

@[always_inline]
instance : Monad (ParsecT ι m) where
  pure := Parsec.pure
  bind := Parsec.bind

@[always_inline, inline, expose]
def lift (t : m α) : ParsecT ι m α := fun s => do let a ← t; pure (.success s a)

instance : MonadLift m (ParsecT ι m) where
  monadLift := lift

/--
Try `p`, and if it fails without consuming input, run `q ()` instead.
-/
@[always_inline, inline]
def orElse (p : ParsecT ι m α) (q : Unit → ParsecT ι m α) : ParsecT ι m α :=
  tryCatch p pure q

/--
Attempt to parse with `p`, but don't consume input on failure.
-/
@[always_inline, inline]
def attempt (p : ParsecT ι m α) : ParsecT ι m α := fun it => do
  match ← p it with
  | .success rem res => pure <| .success rem res
  | .error _ err => pure <| .error it err

@[always_inline]
instance : Alternative (ParsecT ι m) where
  failure := fail ""
  orElse := orElse

/--
Succeeds only if input is at end-of-file.
-/
@[inline]
def eof : ParsecT ι m Unit := fun it =>
  if Input.hasNext it then
    pure <| .error it (.other "expected end of input")
  else
    pure <| .success it ()

@[inline]
def isEof : ParsecT ι m Bool := fun it =>
  pure <| .success it (!Input.hasNext it)

@[specialize]
partial def manyCore (p : ParsecT ι m α) (acc : Array α) : ParsecT ι m <| Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : ParsecT ι m α) : ParsecT ι m <| Array α := manyCore p #[]

@[inline]
def many1 (p : ParsecT ι m α) : ParsecT ι m <| Array α := do manyCore p #[← p]

/--
Gets the next input element.
-/
@[inline]
def any : ParsecT ι m elem := fun it =>
  if h : Input.hasNext it then
    let c := Input.curr' it h
    let it' := Input.next' it h
    pure <| .success it' c
  else
    pure <| .error it .eof

/--
Checks if the next input element matches some condition.
-/
@[inline]
def satisfy (p : elem → Bool) : ParsecT ι m elem := attempt do
  let c ← any
  if p c then return c else fail "condition not satisfied"

/--
Fails if `p` succeeds, otherwise succeeds without consuming input.
-/
@[inline]
def notFollowedBy (p : ParsecT ι m α) : ParsecT ι m Unit := fun it => do
  match ← p it with
  | .success _ _ => pure <| .error it (.other "")
  | .error _ _ => pure <| .success it ()

/--
Peeks at the next element, returns `some` if exists else `none`, does not consume input.
-/
@[inline]
def peek? : ParsecT ι m (Option elem) := fun it =>
  if h : Input.hasNext it then
    pure <| .success it (some <| Input.curr' it h)
  else
    pure <|  .success it none

/--
Peeks at the next element, returns `some elem` if it satisfies `p`, else `none`. Does not consume input.
-/
@[inline]
def peekWhen? (p : elem → Bool) : ParsecT ι m (Option elem) := do
  let some data ← peek?
    | return none

  if p data then
    return some data
  else
    return none

/--
Peeks at the next element, errors on EOF, does not consume input.
-/
@[inline]
def peek! : ParsecT ι m elem := fun it =>
  if h : Input.hasNext it then
    pure <| .success it (Input.curr' it h)
  else
    pure <| .error it .eof

/--
Peeks at the next element or returns a default if at EOF, does not consume input.
-/
@[inline]
def peekD (default : elem) : ParsecT ι m elem := fun it =>
  if h : Input.hasNext it then
    pure <| .success it (Input.curr' it h)
  else
    pure <| .success it default

/--
Consumes one element if available, otherwise errors on EOF.
-/
@[inline]
def skip : ParsecT ι m Unit := fun it =>
  if h : Input.hasNext it then
    pure <| .success (Input.next' it h) ()
  else
    pure <| .error it .eof

/--
Parses zero or more chars with `p`, accumulates into a string.
-/
@[specialize]
partial def manyCharsCore (p : ParsecT ι m Char) (acc : String) : ParsecT ι m String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

/--
Parses zero or more chars with `p` into a string.
-/
@[inline]
def manyChars (p : ParsecT ι m Char) : ParsecT ι m String := do
  manyCharsCore p ""

/--
Parses one or more chars with `p` into a string, errors if none.
-/
@[inline]
def many1Chars (p : ParsecT ι m Char) : ParsecT ι m String := do
  manyCharsCore p (← p).toString

end Parsec
end Internal
end Std
