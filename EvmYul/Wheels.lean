import FastMemset

import EvmYul.UInt256
import Mathlib.Data.Finmap

-- (195)
def BE : ℕ → ByteArray := List.toByteArray ∘ EvmYul.toBytesBigEndian

namespace EvmYul

def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val
  ByteArray.zeroes ⟨32 - b.size⟩ ++ b

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

abbrev AccountAddress : Type := Fin AccountAddress.size

instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

-- abbrev Storage : Type := Finmap (λ _ : UInt256 ↦ UInt256)
-- abbrev Storage : Type := Finmap (λ _ : UInt256 ↦ UInt256)

instance : Inhabited AccountAddress := ⟨Fin.ofNat 0⟩

namespace AccountAddress

def ofNat (n : ℕ) : AccountAddress := Fin.ofNat n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat (v.val % AccountAddress.size)
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat n⟩

def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ByteArray.zeroes ⟨20 - b.size⟩ ++ b

end AccountAddress

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

instance : Repr ByteArray where
  reprPrec s _ := toHex s

/--
  Is an enumerate type, but nat is okay for now TODO(model properly)
-/
def ChainID : Type := Nat
  deriving Repr

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

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

/-- Add `0`s to make the hex representation valid for `ByteArray.ofBlob` -/
def padLeft (n : ℕ) (s : String) :=
  let l := s.length
  if l < n then String.replicate (n - l) '0' ++ s else s

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
  -- TODO: Shouldn't (`e` - `b`) be < `2^64` instead of `e` since eventually `a.copySlice b empty 0 (e - b)` is called?
  if b < 2^64 && e < 2^64
  then a.extract b e -- NB only when `b` and `e` are sufficiently small
  else ⟨⟨a.toList.drop b |>.take (e - b)⟩⟩

def ByteArray.readBytes (source : ByteArray) (start size : ℕ) : ByteArray :=
  let read :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  read ++ ByteArray.zeroes ⟨size - read.size⟩

inductive 𝕋 :=
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋

private def R_b (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x.get! 0 < 128 then some x
  else
    if x.size < 56 then some <| [⟨128 + x.size⟩].toByteArray ++ x
    else
      if x.size < 2^64 then
        let be := BE x.size
        some <| [⟨183 + be.size⟩].toByteArray ++ be ++ x
      else none

mutual

private def s (l : List 𝕋) : Option ByteArray :=
  match l with
    | [] => some .empty
    | t :: ts =>
      match RLP t, s ts with
        | none     , _         => none
        | _        , none      => none
        | some rlpₗ, some rlpᵣ => rlpₗ ++ rlpᵣ

def R_l (l : List 𝕋) : Option ByteArray :=
  match s l with
    | none => none
    | some s_x =>
      if s_x.size < 56 then
        some <| [⟨192 + s_x.size⟩].toByteArray ++ s_x
      else
        if s_x.size < 2^64 then
          let be := BE s_x.size
          some <| [⟨247 + be.size⟩].toByteArray ++ be ++ s_x
        else none

def RLP (t : 𝕋) : Option ByteArray :=
  match t with
    | .𝔹 ba => R_b ba
    | .𝕃 l => R_l l

end

example :
  (RLP (.𝔹 (EvmYul.toBytesBigEndian 123456789).toByteArray) |>.map toHex) == some "84075bcd15"
:= by native_decide

example :
  RLP (.𝔹 .empty) == ByteArray.mk #[0x80]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x78])) == ByteArray.mk #[0x78]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x80])) == ByteArray.mk #[0x81, 0x80]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x83])) == ByteArray.mk #[0x81, 0x83]
:= by  native_decide

private def fiftyFiveBytes : List UInt8 := List.replicate 55 0x83
example :
  RLP (.𝔹 ⟨⟨fiftyFiveBytes⟩⟩) == some ⟨⟨0xB7 :: fiftyFiveBytes⟩⟩
:= by  native_decide

-- private def largeBytes : List UInt8 := List.replicate (2^20) 0x83
-- example :
--   RLP (.𝔹 ⟨⟨largeBytes⟩⟩) == some ⟨⟨0xBA :: 0x10 :: 0x00 :: 0x00 :: largeBytes⟩⟩
-- := by  native_decide

example :
  RLP (.𝔹 (BE 0)) == ByteArray.mk #[0x80]
:= by  native_decide

example :
  RLP (.𝔹 (BE 255)) == ByteArray.mk #[0x81, 0xff]
:= by  native_decide

example :
  RLP (.𝕃 []) == ByteArray.mk #[0xC0]
:= by native_decide

private def hello : Array UInt8 := #[104, 101, 108, 108, 111]
private def how : Array UInt8 := #[104, 111, 119]
private def are : Array UInt8 := #[97, 114, 101]
private def you : Array UInt8 := #[121, 111, 117]
private def doing : Array UInt8 := #[100, 111, 105, 110, 103]

example :
  RLP (.𝕃 [.𝔹 (ByteArray.mk hello)]) ==
    ByteArray.mk (#[0xC6, 0x85] ++ hello)
:= by  native_decide

example :
  RLP (.𝕃 [.𝔹 (BE 255)]) == ByteArray.mk #[0xC2, 0x81, 0xff]
:= by  native_decide

example :
  RLP (.𝕃 (List.replicate 5 (.𝔹 ⟨hello⟩) ++ List.replicate 5 (.𝔹 (BE 35))))
    ==
  ByteArray.mk
    ( #[0xE3]
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[35, 35, 35, 35, 35]
    )
:= by native_decide

example :
  RLP (.𝕃 (List.replicate 10 (.𝔹 (BE 35)) ++ List.replicate 10 (.𝔹 ⟨hello⟩)))
    ==
  ByteArray.mk
    ( #[0xF8] ++ #[70]
      ++ #[35, 35, 35, 35, 35, 35, 35, 35, 35, 35]
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
    )
:= by native_decide

private def nestedSequence : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝔹 ⟨you⟩, .𝕃 [.𝔹 ⟨doing⟩]]]
    ]

example :
  RLP nestedSequence
    ==
  ByteArray.mk
    ( #[0xdd, 0x85]
      ++ hello
      ++ #[0x81,0xff,0xd4,0x83]
      ++ how
      ++ #[0xcf,0x83]
      ++ are
      ++ #[0x83]
      ++ you
      ++ #[0xc6, 0x85]
      ++ doing
      )
:= by native_decide

private def willFail₁ : 𝕋 := .𝔹 (BE 123)
private def willFail₂ : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝕃 [.𝔹 ⟨you⟩, .𝔹 (BE 123)]]]
    ]
