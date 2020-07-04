/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.List.Control
import Init.Data.UInt
import Init.Data.Option.Basic
universes u

structure ByteArray :=
(data : Array UInt8)

attribute [extern "lean_byte_array_mk"] ByteArray.mk
attribute [extern "lean_byte_array_data"] ByteArray.data

namespace ByteArray
@[extern "lean_mk_empty_byte_array"]
def mkEmpty (c : @& Nat) : ByteArray :=
{ data := #[] }

def empty : ByteArray :=
mkEmpty 0

instance : Inhabited ByteArray :=
⟨empty⟩

@[extern "lean_byte_array_push"]
def push : ByteArray → UInt8 → ByteArray
| ⟨bs⟩, b => ⟨bs.push b⟩

@[extern "lean_byte_array_size"]
def size : (@& ByteArray) → Nat
| ⟨bs⟩ => bs.size

@[extern "lean_byte_array_get"]
def get! : (@& ByteArray) → (@& Nat) → UInt8
| ⟨bs⟩, i => bs.get! i

@[extern "lean_byte_array_set"]
def set! : ByteArray → (@& Nat) → UInt8 → ByteArray
| ⟨bs⟩, i, b => ⟨bs.set! i b⟩

def isEmpty (s : ByteArray) : Bool :=
s.size == 0

partial def toListAux (bs : ByteArray) : Nat → List UInt8 → List UInt8
| i, r =>
  if i < bs.size then
    toListAux (i+1) (bs.get! i :: r)
  else
    r.reverse

def toList (bs : ByteArray) : List UInt8 :=
toListAux bs 0 []

private def convertUtf8Byte (utf8 : ByteArray) (i : Nat) : Option UInt8 := do
let tailPrefixMask : UInt8 := 0b11000000;
let tailPrefix     : UInt8 := 0b10000000;
let tailMask       : UInt8 := 0b00111111;
byte ← utf8.data.get? i;
guard (byte.land tailPrefixMask = tailPrefix);
some (byte.land tailMask)

private def concatUtf8Bytes (xs : List UInt8) : UInt32 :=
let tailOffset := 6;
xs.foldr (fun byte acc => (acc.shiftLeft tailOffset).lor byte.toNat.toUInt32) 0

private partial def utf8ToStringAux : Nat → ByteArray → Option (List Char)
| i, utf8 =>
  -- mask to extract prefix × expected prefix of first byte × mask to extract data from first byte
  let patterns : List (UInt8 × UInt8 × UInt8) := [
    (0b10000000, 0b00000000, 0b01111111),
    (0b11100000, 0b11000000, 0b00011111),
    (0b11110000, 0b11100000, 0b00001111),
    (0b11111000, 0b11110000, 0b00000111)
  ];
  if i < utf8.size then do
    let byte := utf8.get! i;
    (charVal, nextCharOffset) ← ((List.range patterns.length).zip patterns).firstM (fun ⟨j, prefixMask, pre, dataMask⟩ => do
      guard (byte.land prefixMask = pre);
      let msb := byte.land dataMask;
      -- parse the rest of the bytes
      bytes ← (List.range j).mapM (fun k => convertUtf8Byte utf8 (i+k+1));
      some (concatUtf8Bytes (msb :: bytes), j+1));
    guard (isValidChar charVal);
    tail ← utf8ToStringAux (i+nextCharOffset) utf8;
    some ((Char.ofNat charVal.toNat) :: tail)
  else
    some []

def utf8ToString (utf8 : ByteArray) : Option String := do
chars ← utf8ToStringAux 0 utf8;
some ⟨chars⟩

end ByteArray

def List.toByteArrayAux : List UInt8 → ByteArray → ByteArray
| [],    r => r
| b::bs, r => List.toByteArrayAux bs (r.push b)

def List.toByteArray (bs : List UInt8) : ByteArray :=
bs.toByteArrayAux ByteArray.empty

instance : HasToString ByteArray :=
⟨fun bs => bs.toList.toString⟩
