import EvmYul.UInt256

import Mathlib.Data.Finmap

namespace EvmYul

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def Address.size : Nat := 1461501637330902918203684832716283019655932542976

abbrev Address : Type := Fin Address.size

-- abbrev Storage : Type := Finmap (λ _ : UInt256 ↦ UInt256)

instance : Inhabited Address := ⟨Fin.ofNat 0⟩

namespace Address

def ofNat {n : ℕ} : Address := Fin.ofNat n
def ofUInt256 (v : UInt256) : Address := Fin.ofNat (v.val % Address.size)
instance {n : Nat} : OfNat Address n := ⟨Fin.ofNat n⟩

end Address

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

/--
  Is an enumerate type, but nat is okay for now TODO(model properly)
-/
def ChainID : Type := Nat

deriving instance DecidableEq for ChainID
deriving instance Inhabited for ChainID

def Identifier := String
instance : ToString Identifier := inferInstanceAs (ToString String)
instance : Inhabited Identifier := inferInstanceAs (Inhabited String)
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)
instance : Repr Identifier := inferInstanceAs (Repr String)

namespace NaryNotation

scoped syntax "!nary[" ident "^" num "]" : term

open Lean in
scoped macro_rules
  | `(!nary[ $idn:ident ^ $nat:num ]) =>
    let rec go (n : ℕ) : MacroM Term :=
      match n with
        | 0     => `($idn)
        | n + 1 => do `($idn → $(←go n))
    go nat.getNat

end NaryNotation

namespace Primop

section

open NaryNotation

def Nullary    := !nary[UInt256 ^ 0]
def Unary      := !nary[UInt256 ^ 1]
def Binary     := !nary[UInt256 ^ 2]
def Ternary    := !nary[UInt256 ^ 3]
def Quaternary := !nary[UInt256 ^ 4]

end

end Primop

end EvmYul

/--
TODO(rework later to a sane version)
-/
instance : DecidableEq ByteArray := by
  rintro ⟨a⟩ ⟨b⟩
  rw [ByteArray.mk.injEq]
  apply decEq

def Option.option {α β : Type} (dflt : β) (f : α -> β) : Option α → β
  | .none => dflt
  | .some x => f x

def Option.toExceptWith {α β : Type} (dflt : β) (x : Option α) : Except β α :=
  x.option (.error dflt) Except.ok

def ByteArray.get? (self : ByteArray) (n : Nat) : Option UInt8 :=
  if h : n < self.size
  then self.get ⟨n, h⟩
  else .none

partial def Nat.toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (toHex (n / 16)) ++ hexDigitRepr (n % 16)

/--
TODO - Well this is ever so slightly unfortunate.
It appears to be the case that some (all?) definitions that have C++ implementations
use 64bit-width integers to hold numeric arguments.

When this assumption is broken, e.g. `n : Nat := 2^64`, the Lean (4.9.0) gives
inernal out of memory error.

This implementation works around the issue at the price of using a slower implementation
in case either of the arguments is too big.
-/
def ByteArray.extract' (a : ByteArray) (b e : Nat) : ByteArray :=
  if b < 2^64 && e < 2^64
  then a.extract b e -- NB only when `b` and `e` are sufficiently small
  else ⟨⟨a.toList.drop b |>.take (e - b)⟩⟩
