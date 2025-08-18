import EvmYul.UInt256
import Mathlib.Data.Finmap
import EvmYul.FFI.ffi

-- (195)
def BE : ℕ → ByteArray := List.toByteArray ∘ EvmYul.toBytesBigEndian

namespace EvmYul

def chainId : ℕ := 1

def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val.toNat
  ffi.ByteArray.zeroes ⟨32 - b.size⟩ ++ b

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero AccountAddress.size where
  out := (by unfold AccountAddress.size; simp)

abbrev AccountAddress : Type := Fin AccountAddress.size

instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

instance : Inhabited AccountAddress := ⟨Fin.ofNat _ 0⟩

namespace AccountAddress

def ofNat (n : ℕ) : AccountAddress := Fin.ofNat _ n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.val % AccountAddress.size)
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩

def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ffi.ByteArray.zeroes ⟨20 - b.size⟩ ++ b

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
  then self.get n h
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

def HexPrefix := "0x"

def TargetSchedule := "Cancun"

def isHexDigitChar (c : Char) : Bool :=
  '0' <= c && c <= '9' || 'a' <= c.toLower && c.toLower <= 'f'

def cToHex? (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9'
  then .ok <| c.toString.toNat!
  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f'
        then let Δ := c.toLower.toNat - 'a'.toNat
            .ok <| 10 + Δ
        else .error s!"Not a hex digit: {c}"

def ofHex? : List Char → Except String UInt8
  | [] => pure 0
  | [msb, lsb] => do pure ∘ UInt8.ofNat <| (← cToHex? msb) * 16 + (← cToHex? lsb)
  | _ => throw "Need two hex digits for every byte."

def Blob := String

instance : Inhabited Blob := inferInstanceAs (Inhabited String)

def Blob.toString : Blob → String := λ blob ↦ blob

instance : ToString Blob := ⟨Blob.toString⟩

def getBlob? (s : String) : Except String Blob :=
  if isHex s then
    let rest := s.drop HexPrefix.length
    if rest.any (not ∘ isHexDigitChar)
    then .error "Blobs must consist of valid hex digits."
    else .ok rest.toLower
  else .error "Input does not begin with 0x."
  where
    isHex (s : String) := s.startsWith HexPrefix

def getBlob! (s : String) : Blob := getBlob? s |>.toOption.get!

def ByteArray.ofBlob (self : Blob) : Except String ByteArray := do
  let chunks ← self.toList.toChunks 2 |>.mapM ofHex?
  pure ⟨chunks.toArray⟩

def ByteArray.readBytes (source : ByteArray) (start size : ℕ) : ByteArray :=
  let read :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  read ++ ffi.ByteArray.zeroes ⟨size - read.size⟩

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
    read ++ ffi.ByteArray.zeroes ⟨len - read.size⟩

inductive 𝕋 where
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋
  deriving Repr, BEq


def lengthRLP (rlp : ByteArray) : Option ℕ :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      some 1
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        some (1 + strLen)
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          some (1 + lenOfStrLen + strLen)
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            some (1 + listLen)
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              some (1 + lenOfListLen + listLen)
            else
              none

partial def separateListRLP (rlp : ByteArray) : Option (List ByteArray) := do
  if rlp.isEmpty then pure []
  else
    let headLen ← lengthRLP rlp
    let head := rlp.readWithoutPadding 0 headLen
    let tail ← separateListRLP (rlp.readWithoutPadding headLen rlp.size)
    pure <| head :: tail

def oneStepRLP (rlp : ByteArray) : Option (Sum ByteArray (List ByteArray)) :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      let data := .inl ⟨#[rlp₀]⟩
      some data
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        let data := .inl (rlp.readWithoutPadding 1 strLen)
        some data
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          let data := .inl (rlp.readWithoutPadding (1 + lenOfStrLen) strLen)
          some data
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            let list ← separateListRLP (rlp.readWithoutPadding 1 listLen)
            some <| .inr list
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              let list ← separateListRLP (rlp.readWithoutPadding (1 + lenOfListLen) listLen)
              some <| .inr list
            else
              none

partial def deserializeRLP (rlp : ByteArray) : Option 𝕋 := do
  match ← oneStepRLP rlp with
    | .inl byteArray =>
      some (.𝔹 byteArray)
    | .inr list =>
      let l ← list.mapM deserializeRLP
      some (.𝕃 l)

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

def myByteArray : ByteArray := ⟨#[1, 2, 3]⟩

def ByteArray.write
  (source : ByteArray)
  (sourceAddr : ℕ)
  (dest : ByteArray)
  (destAddr len : ℕ)
  : ByteArray
:=
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (ffi.ByteArray.zeroes ⟨len⟩).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      let endPaddingAddr := min dest.size (destAddr + len)
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      let sourcePadding := ffi.ByteArray.zeroes ⟨sourcePaddingLength⟩
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding := ffi.ByteArray.zeroes ⟨destPaddingLength⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)
