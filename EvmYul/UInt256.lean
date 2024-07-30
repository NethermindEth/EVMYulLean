import Init.Data.Nat.Div
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace EvmYul

def UInt256.size : ℕ := 115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size := ⟨by decide⟩

abbrev UInt256 := Fin UInt256.size

instance : SizeOf UInt256 where sizeOf := 1

namespace UInt256

def ofNat (n : ℕ) : UInt256 := Fin.ofNat n
instance {n : ℕ} : OfNat UInt256 n := ⟨UInt256.ofNat n⟩
instance : Inhabited UInt256 := ⟨0⟩

end UInt256

end EvmYul

section CastUtils

open EvmYul UInt256

abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 := ⟨a.1, Nat.lt_trans a.1.2 (by decide)⟩
def Bool.toUInt256 (b : Bool) : UInt256 := if b then 1 else 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = 1 := rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = 0 := rfl

end CastUtils

namespace EvmYul

namespace UInt256

def add (a b : UInt256) : UInt256 := a.1 + b.1
def sub (a b : UInt256) : UInt256 := a.1 - b.1
def mul (a b : UInt256) : UInt256 := a.1 * b.1
def div (a b : UInt256) : UInt256 := a.1 / b.1
def mod (a b : UInt256) : UInt256 := a.1 % b.1
def modn (a : UInt256) (n : ℕ) : UInt256 := Fin.modn a.1 n
def land (a b : UInt256) : UInt256 := Fin.land a.1 b.1
def lor (a b : UInt256) : UInt256 := Fin.lor a.1 b.1
def xor (a b : UInt256) : UInt256 := Fin.xor a.1 b.1
def shiftLeft (a b : UInt256) : UInt256 := a.1 <<< (modn b 256).1
def shiftRight (a b : UInt256) : UInt256 := a.1 >>> (modn b 256).1
-- def lt (a b : UInt256) : Prop := a.1 < b.1
-- def le (a b : UInt256) : Prop := a.1 ≤ b.1
def log2 (a : UInt256) : UInt256 := Fin.log2 a.1
def floor (a : UInt256) : UInt256 := Fin.ofNat (Nat.floor a.1)

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩
-- instance : LT UInt256 := ⟨UInt256.lt⟩
-- instance : LE UInt256 := ⟨UInt256.le⟩

def complement (a : UInt256) : UInt256 := 0-(a + 1)

instance : Complement UInt256 := ⟨EvmYul.UInt256.complement⟩

private def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2) 
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux 1 b n.1

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : Xor UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩
instance : DecidableEq UInt256 := decEq

def decLt (a b : UInt256) : Decidable (a < b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n < m))

def decLe (a b : UInt256) : Decidable (a ≤ b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt256) : Decidable (a < b) := decLt _ _
instance (a b : UInt256) : Decidable (a ≤ b) := UInt256.decLe a b
instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

def toNat (n : UInt256) : ℕ := n.1
def eq0 (a : UInt256) : Bool := a = 0
def lnot (a : UInt256) : UInt256 := (UInt256.size - 1) - a

def byteAt (a b : UInt256) : UInt256 :=
  -- dbg_trace "BYTE AT"
  b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& 0xFF

def sgn (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a
  then -1
  else
    if a = 0
    then 0
    else 1

def abs (a : UInt256) : UInt256 := 
  if 2 ^ 255 <= a
  then a * -1
  else a

def bigUInt : UInt256 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a then
    if 2 ^ 255 <= b then
      abs a / abs b
    else (abs a / b) * -1
  else
    if 2 ^ 255 <= b then
       (a / abs b) * -1
    else a / b

#eval sdiv 1 4

def smod (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a
  then if 2 ^ 255 <= b
       then (abs a) % (abs b)
       else -1 * (abs a) % b
  else if 2 ^ 255 <= b
       then -1 * a % (abs b)
       else a % b

def sltBool (a b : UInt256) : Bool :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b ≥ 2 ^ 255 then false
    else a < b

def sgtBool (a b : UInt256) : Bool :=
  if a ≥ 2 ^ 255 then
    if b ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b ≥ 2 ^ 255 then true
    else a > b

abbrev fromBool := Bool.toUInt256

def slt (a b : UInt256) :=
  fromBool (sltBool a b)

def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

def sar (a b : UInt256) : UInt256 :=
  if sltBool a 0
  then UInt256.complement (UInt256.complement a >>> b)
  else a >>> b

private partial def dbg_toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (dbg_toHex (n / 16)) ++ hexDigitRepr (n % 16)

def signextend (a b : UInt256) : UInt256 :=
  if a ≤ 31 then
    let test_bit := a * 8 + 7
    let sign_bit := 1 <<< test_bit
    if b &&& sign_bit ≠ 0 then
      b ||| (UInt256.size.toUInt256 - sign_bit)
    else b &&& (sign_bit - 1)
  else b

def addMod (a b c : UInt256) : UInt256 :=
  if c = 0 then 0 else
  Fin.mod (a + b) c

def mulMod (a b c : UInt256) : UInt256 :=
  if c = 0 then 0 else
  Fin.mod (a * b) c

def exp (a b : UInt256) : UInt256 := pow a b
  -- a ^ b.val

def lt (a b : UInt256) :=
  fromBool (a < b)

def gt (a b : UInt256) :=
  fromBool (a > b)

def eq (a b : UInt256) :=
  fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (a = 0)

end UInt256

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.val.val + 2^8 * fromBytes' bs

def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse

variable {bs : List UInt8}
         {n : ℕ}

-- | A bound for the natural number value of a list of bytes.
private lemma fromBytes'_le : fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold fromBytes'; simp
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.val.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

-- | The natural number value of a length 32 list of bytes is < 2^256.
private lemma fromBytes'_UInt256_le (h : bs.length = 32) : fromBytes' bs < 2^256 := by
    have h' := @fromBytes'_le bs
    rw [h] at h'
    exact h'

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := ⟨Nat.mod n UInt8.size, Nat.mod_lt _ (by linarith)⟩
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
private lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [toBytes']
    | .succ n =>
      unfold toBytes'
      simp [Nat.succ_le_succ_iff]
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
private lemma toBytes'_UInt256_le (h : n < UInt256.size) : (toBytes' n).length ≤ 32 := toBytes'_le h

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

-- | The length of a `zeroPadBytes` call is its first argument.
lemma zeroPadBytes_len (h : bs.length ≤ n) : (zeroPadBytes n bs).length = n := by
  unfold zeroPadBytes
  aesop

-- | Appending a bunch of zeroes to a little-endian list of bytes doesn't change its value.
@[simp]
private lemma extend_bytes_zero : fromBytes' (bs ++ List.replicate n 0) = fromBytes' bs := by
  induction bs with
  | nil =>
    simp [fromBytes']
    induction n with
    | zero => simp [List.replicate, fromBytes']
    | succ _ ih => simp [List.replicate, fromBytes']; norm_cast
  | cons _ _ ih => simp [fromBytes', ih]

-- | The ℕ value of a little-endian list of bytes is invariant under right zero-padding up to length 32.
@[simp]
private lemma fromBytes'_zeroPadBytes_32_eq : fromBytes' (zeroPadBytes 32 bs) = fromBytes' bs := extend_bytes_zero

-- | Casting a natural number to a list of bytes and back is the identity.
@[simp]
private lemma fromBytes'_toBytes' {x : ℕ} : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp only
    have := Nat.div_lt_self (Nat.zero_lt_succ n) (by decide : 1 < UInt8.size)
    rw [fromBytes'_toBytes']
    simp [UInt8.size, add_comm]
    apply Nat.div_add_mod

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

private lemma fromBytes_was_good_all_year_long
  (h : bs.length ≤ 32) : fromBytes' bs < 2^256 := by
  have h' := @fromBytes'_le bs
  rw [pow_mul] at h'
  refine lt_of_lt_of_le (b := (2 ^ 8) ^ List.length bs) h' ?lenBs
  case lenBs => rw [←pow_mul]; exact pow_le_pow_right (by decide) (by linarith)

@[simp]
lemma fromBytes_wasnt_naughty : fromBytes! bs < 2^256 := fromBytes_was_good_all_year_long (by simp)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  ⟨fromBytes! bs, fromBytes_wasnt_naughty⟩

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.1)

@[simp]
lemma length_toBytes! {n : UInt256} : (toBytes! n).length = 32 := zeroPadBytes_len (toBytes'_UInt256_le n.2)

def uInt256OfByteArray' (arr : ByteArray) : UInt256 := Id.run do
  let mut acc : ℕ := 0
  let mut exp : ℕ := arr.size - 1
  for byte in arr do
    acc := acc + byte.toNat * 2 ^ (8 * exp)
    exp := exp - 1
  return acc

def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  fromBytes' arr.data.toList.reverse

end EvmYul
