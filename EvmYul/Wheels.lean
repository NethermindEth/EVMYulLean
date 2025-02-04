import FastMemset

import EvmYul.UInt256
import Mathlib.Data.Finmap

-- (195)
def BE : ℕ → ByteArray := List.toByteArray ∘ EvmYul.toBytesBigEndian

namespace EvmYul

def chainId : ℕ := 1

def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val.toNat
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

def ByteArray.readWithoutPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if addr ≥ source.size then .empty else
    let len := min len source.size
    source.extract addr (addr + len)

private def inf := 2^66

def ByteArray.readWithPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if len ≥ 2^64 then
    panic! s!"ByteArray.readWithPadding: can not handle byte arrays of length {len}"
  else
    let read := source.readWithoutPadding addr len
    read ++ ByteArray.zeroes ⟨len - read.size⟩

inductive 𝕋 :=
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋
  deriving Repr, BEq

mutual

partial def deserializeListRLP (rlp : ByteArray) : Option (List 𝕋) := do
  if rlp.isEmpty then pure []
  else
    let (headLen, head) ← deserializeRLP₀ rlp
    -- dbg_trace s!"headLen {headLen}"
    -- dbg_trace s!"repr head {repr head}"
    let tail ← deserializeListRLP (rlp.readWithoutPadding headLen rlp.size)
    pure <| head :: tail

partial def deserializeRLP₀ (rlp : ByteArray) : Option (ℕ × 𝕋) :=
  let len := rlp.size
  if len = 0 then none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      let data := .𝔹 ⟨#[rlp₀]⟩
      some (1, data)
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        let data := .𝔹 (rlp.readWithoutPadding 1 strLen)
        some (1 + strLen, data)
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          let data := .𝔹 (rlp.readWithoutPadding (1 + lenOfStrLen) strLen)
          some (1 + lenOfStrLen + strLen, data)
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            let list ← deserializeListRLP (rlp.readWithoutPadding 1 listLen)
            some (1 + listLen, .𝕃 list)
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              let list ← deserializeListRLP (rlp.readWithoutPadding (1 + lenOfListLen) listLen)
              some (1 + lenOfListLen + listLen, .𝕃 list)
            else none

end

partial def deserializeRLP (rlp : ByteArray) : Option 𝕋 :=
  (deserializeRLP₀ rlp).map Prod.snd

example : deserializeRLP₀ .empty == none := by native_decide
example : deserializeRLP₀ ⟨#[0]⟩ == some (1, .𝔹 ⟨#[0]⟩) := by native_decide
example : deserializeRLP₀ ⟨#[127]⟩ == some (1, .𝔹 ⟨#[127]⟩) := by native_decide
example : deserializeRLP₀ ⟨#[128]⟩ == some (1, .𝔹 .empty) := by native_decide
example :
  deserializeRLP₀ (⟨#[128 + 55]⟩ ++ ByteArray.zeroes ⟨55⟩) ==
    some (56, .𝔹 (ByteArray.zeroes ⟨55⟩))
  := by native_decide
example :
  deserializeRLP₀ (⟨#[183 + 1, 56]⟩ ++ ByteArray.zeroes ⟨56⟩) ==
    some (58, .𝔹 (ByteArray.zeroes ⟨56⟩))
  := by native_decide

example :
  deserializeRLP₀ (⟨#[192 + 3, 0, 127, 128]⟩) ==
    some (4, 𝕋.𝕃 [𝕋.𝔹 ⟨#[0x00]⟩, 𝕋.𝔹 ⟨#[0x7f]⟩, 𝕋.𝔹 .empty])
  := by native_decide

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

private def data₁ : 𝕋 := .𝔹 (EvmYul.toBytesBigEndian 123456789).toByteArray
private def rlp₁ : ByteArray := BE 0x84075bcd15
example : RLP data₁ == rlp₁ := by native_decide
example : deserializeRLP rlp₁ == data₁ := by native_decide

private def data₂ : 𝕋 := .𝔹 .empty
private def rlp₂ : ByteArray := ByteArray.mk #[0x80]
example : RLP data₂ == rlp₂ := by  native_decide
example : deserializeRLP rlp₂ == data₂ := by  native_decide

private def data₃ : 𝕋 := .𝔹 (ByteArray.mk #[0x78])
private def rlp₃ : ByteArray := ByteArray.mk #[0x78]
example : RLP data₃ == rlp₃ := by native_decide
example : deserializeRLP rlp₃ == data₃:= by native_decide

private def data₄ : 𝕋 := .𝔹 (ByteArray.mk #[0x80])
private def rlp₄ : ByteArray := ByteArray.mk #[0x81, 0x80]
example : RLP data₄ == rlp₄ := by native_decide

private def data₅ : 𝕋 := .𝔹 (ByteArray.mk #[0x83])
private def rlp₅ : ByteArray := ByteArray.mk #[0x81, 0x83]
example : RLP data₅ == rlp₅ := by  native_decide
example : deserializeRLP rlp₅ == data₅ := by native_decide

private def fiftyFiveBytes : List UInt8 := List.replicate 55 0x83
private def data₆ : 𝕋 := .𝔹 ⟨⟨fiftyFiveBytes⟩⟩
private def rlp₆ : ByteArray := ⟨⟨0xB7 :: fiftyFiveBytes⟩⟩
example : RLP data₆ == rlp₆ := by  native_decide
example : deserializeRLP rlp₆ == data₆ := by  native_decide

-- private def largeBytes : List UInt8 := List.replicate (2^20) 0x83
-- example :
--   RLP (.𝔹 ⟨⟨largeBytes⟩⟩) == some ⟨⟨0xBA :: 0x10 :: 0x00 :: 0x00 :: largeBytes⟩⟩
-- := by  native_decide

private def data₇ : 𝕋 := .𝔹 (BE 0)
private def rlp₇ : ByteArray := ByteArray.mk #[0x80]
example : RLP data₇ == rlp₇ := by  native_decide
example : deserializeRLP rlp₇ == data₇ := by  native_decide

private def data₈ : 𝕋 := .𝔹 (BE 255)
private def rlp₈ : ByteArray := ByteArray.mk #[0x81, 0xff]
example : RLP data₈ == rlp₈ := by native_decide
example : deserializeRLP rlp₈ == data₈ := by native_decide

private def data₉ : 𝕋 := .𝕃 []
private def rlp₉ : ByteArray := ByteArray.mk #[0xC0]
example : RLP data₉ == rlp₉ := by native_decide
example : deserializeRLP rlp₉ == data₉ := by native_decide

private def hello : Array UInt8 := #[104, 101, 108, 108, 111]
private def how : Array UInt8 := #[104, 111, 119]
private def are : Array UInt8 := #[97, 114, 101]
private def you : Array UInt8 := #[121, 111, 117]
private def doing : Array UInt8 := #[100, 111, 105, 110, 103]

private def data₁₀ : 𝕋 := .𝕃 [.𝔹 (ByteArray.mk hello)]
private def rlp₁₀ : ByteArray := ByteArray.mk (#[0xC6, 0x85] ++ hello)
example : RLP data₁₀ == rlp₁₀ := by native_decide
example : deserializeRLP rlp₁₀ == data₁₀ := by native_decide

private def data₁₁ : 𝕋 := .𝕃 [.𝔹 (BE 255)]
private def rlp₁₁ : ByteArray := ByteArray.mk #[0xC2, 0x81, 0xff]
example : RLP data₁₁ == rlp₁₁ := by native_decide
example : deserializeRLP rlp₁₁ == data₁₁ := by native_decide

private def data₁₂ : 𝕋 := .𝕃 (List.replicate 5 (.𝔹 ⟨hello⟩) ++ List.replicate 5 (.𝔹 (BE 35)))
private def rlp₁₂ : ByteArray :=
  ByteArray.mk
    ( #[0xE3]
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[35, 35, 35, 35, 35]
    )
example : RLP data₁₂ == rlp₁₂ := by native_decide
example : deserializeRLP rlp₁₂ == data₁₂ := by native_decide

private def data₁₃ : 𝕋 := .𝕃 (List.replicate 10 (.𝔹 (BE 35)) ++ List.replicate 10 (.𝔹 ⟨hello⟩))
private def rlp₁₃ : ByteArray :=
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
example : RLP data₁₃ == rlp₁₃ := by native_decide
example : deserializeRLP rlp₁₃ == data₁₃ := by native_decide

private def nestedSequence : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝔹 ⟨you⟩, .𝕃 [.𝔹 ⟨doing⟩]]]
    ]
private def data₁₄ : 𝕋 := nestedSequence
private def rlp₁₄ : ByteArray :=
  ByteArray.mk
    ( #[0xdd, 0x85]
      ++ hello
      ++ #[0x81, 0xff, 0xd4, 0x83]
      ++ how
      ++ #[0xcf, 0x83]
      ++ are
      ++ #[0x83]
      ++ you
      ++ #[0xc6, 0x85]
      ++ doing
      )
example : RLP data₁₄ == rlp₁₄ := by native_decide
example : deserializeRLP rlp₁₄ == data₁₄ := by native_decide

private def willFail₁ : 𝕋 := .𝔹 (BE 123)
private def willFail₂ : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝕃 [.𝔹 ⟨you⟩, .𝔹 (BE 123)]]]
    ]

-- def block :=
--   deserializeRLP <|
--     BE 0xf902caf9023ca0923fba01f2e1b29d63abab81ef717d07776a4e8b678767b153f3858347b2563fa01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347942adc25665018aa1fe0e6bc666dac8fc2697ff9baa0f0bbeebd9c3c89facd5498ddca48814e61eda52dfa4aa5d02b6e4da17f6e2f6ba09a8994398ec40bc7169e220e12634b530fd8ddc41a5c9e482de8ff9bd7fff03da0755ea5c3322d9143fb00717ab6cb7ec8968fe86941e3ac06ece8dd6ed8071bc5b901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018405f5e100840259e4e18203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b4218080a00000000000000000000000000000000000000000000000000000000000000000f887f885010a8404c4b40094cccccccccccccccccccccccccccccccccccccccc80a43f8390d50000000000000000000000000000000000000000000000000000000000f200fe1ca090af9a14540fa5ce8e271c4726a93c0e64a2125f1e3e53eb46b8d0f5c0bc4483a02e9174f9630017eb53a1e61a294779b8cb8cddc3bef1c25de536f6c746318c5cc0c0

-- #eval block

def myByteArray : ByteArray := ⟨#[1, 2, 3]⟩

def ByteArray.write
  (source : ByteArray)
  (sourceAddr : ℕ)
  (dest : ByteArray)
  (destAddr len : ℕ)
  -- (maxAddress := dest.size)
  : ByteArray
:=
  -- dbg_trace s!"ByteArray.write: source.size = {source.size}, len = {len}"
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (ByteArray.zeroes ⟨len⟩).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      -- dbg_trace s!"practicalLen = {practicalLen}"
      let endPaddingAddr := min dest.size (destAddr + len)
      -- dbg_trace s!"endPaddingAddr = {endPaddingAddr}"
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      -- dbg_trace s!"sourcePaddingLength = {sourcePaddingLength}"
      let sourcePadding := ByteArray.zeroes ⟨sourcePaddingLength⟩
      -- dbg_trace sourcePaddingLength
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding := ByteArray.zeroes ⟨destPaddingLength⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)

example : ByteArray.empty.write inf myByteArray 5 inf = myByteArray := by native_decide
example : ByteArray.empty.write inf myByteArray 1 inf = ⟨#[1, 0, 0]⟩ := by native_decide
example : myByteArray.write 2 myByteArray 0 inf = ⟨#[3, 0, 0]⟩ := by native_decide
example : myByteArray.write inf myByteArray 0 inf = ⟨#[0, 0, 0]⟩ := by native_decide
example : myByteArray.write 0 myByteArray 1 1 = ⟨#[1, 1, 3]⟩ := by native_decide
