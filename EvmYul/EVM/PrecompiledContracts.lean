import EvmYul.Maps.AccountMap
import EvmYul.UInt256
import EvmYul.State.Substate
import EvmYul.State.ExecutionEnv
import EvmYul.EVM.Exception
import EvmYul.Wheels

import EvmYul.EllipticCurves
import EvmYul.SHA256
import EvmYul.RIP160
import EvmYul.BN_ADD
import EvmYul.BN_MUL
import EvmYul.SNARKV
import EvmYul.BLAKE2_F
import EvmYul.PointEval

import EvmYul.FFI.ffi

open EvmYul

def Ξ_ECREC
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 3000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.inputData
    let h := d.readBytes 0 32
    let v := d.readBytes 32 32
    let r := d.readBytes 64 32
    let s := d.readBytes 96 32
    let v' : ℕ := fromByteArrayBigEndian v
    let r' : ℕ := fromByteArrayBigEndian r
    let s' : ℕ := fromByteArrayBigEndian s
    let o :=
      if v' < 27 || 28 < v' || r' = 0 || r' >= secp256k1n || s' = 0 || s' >= secp256k1n then
        .empty
      else
        match ECDSARECOVER h ⟨#[.ofNat v' - 27]⟩ r s with
          | .ok s =>
              ffi.ByteArray.zeroes ⟨12⟩ ++ (KEC s).extract 12 32
          | .error e =>
            dbg_trace s!"Ξ_ECREC failed: {e}"
            .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_SHA256
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.inputData.size
    let ceil := ( l + 31 ) / 32
    60 + 12 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match ffi.SHA256 I.inputData with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_SHA56 failed: {e}"
          .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_RIP160
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.inputData.size
    let ceil := ( l + 31 ) / 32
    600 + 120 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match RIP160 I.inputData with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_RIP160 failed: {e}"
          .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_ID
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.inputData.size
    let ceil := ( l + 31 ) / 32
    15 + 3 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := I.inputData
    (true, σ, g - .ofNat gᵣ, A, o)

def nat_of_slice
  (B: ByteArray)
  (start: ℕ)
  (width: ℕ) : ℕ
:=
  let slice := B.readWithoutPadding start width
  let padding := width - slice.size
  fromByteArrayBigEndian slice <<< (8 * padding)

def expModAux (m : ℕ) (a : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => a % m
  | n@(k + 1) =>
    if n % 2 == 1 then
      expModAux m (a * c % m) (c * c % m) (n / 2)
    else
      expModAux m (a % m)     (c * c % m) (n / 2)

def expMod (m : ℕ) (b : UInt256) (n : ℕ) : ℕ := expModAux m 1 b.toNat n

def Ξ_EXPMOD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let data := I.inputData
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  -- Pseudo laziness
  -- We don't want to call `nat_of_slice` unless we need it
  let exp := λ () ↦ nat_of_slice data (96 + base_length) exp_length

  let gᵣ :=
    let multiplication_complexity x y := ((max x y + 7) / 8) ^ 2
    let adjusted_exp_length :=
      if exp_length ≤ 32 && exp () == 0 then
        0
      else
        if exp_length ≤ 32 then
          Nat.log 2 (exp ())
        else
          let length_part := 8 * (exp_length - 32)
          let bits_part :=
            let exp_head := nat_of_slice data (96 + base_length) 32
            if 32 < exp_length ∧ exp_head != 0 then
              Nat.log 2 exp_head
            else
              0
          length_part + bits_part
    let iterations := max adjusted_exp_length 1
    let G_quaddivisor := 3

    max 200 (multiplication_complexity base_length modulus_length * iterations / G_quaddivisor)

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let modulus := nat_of_slice data (96 + base_length + exp_length) modulus_length
    let o : ByteArray :=
      if modulus_length == 0 || modulus == 0 then
        ffi.ByteArray.zeroes ⟨modulus_length⟩
      else
        let base := nat_of_slice data 96 base_length
        let exp := nat_of_slice data (96 + base_length) exp_length
        let expmod_base := BE (expMod modulus (.ofNat base) exp)
        let expmod_zeroes :=
          if modulus_length ≥ expmod_base.size then
            ffi.ByteArray.zeroes ⟨modulus_length - expmod_base.size⟩
          else
            ByteArray.empty
        expmod_zeroes ++ expmod_base
    (true, σ, g - .ofNat gᵣ, A, o)

private def expmodOutput :=
  let (_, _, _, _, o) :=
    Ξ_EXPMOD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        inputData := l_B ++ l_E ++ l_M ++ B ++ E ++ M
      }
  o
 where
  l_B : ByteArray := UInt256.toByteArray ⟨2⟩
  l_E : ByteArray := UInt256.toByteArray ⟨1⟩
  l_M : ByteArray := UInt256.toByteArray ⟨1⟩
  B : ByteArray := ⟨#[1, 0]⟩ -- 2^8
  E : ByteArray := ⟨#[2]⟩
  M : ByteArray := ⟨#[100]⟩

def Ξ_BN_ADD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 150

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.inputData
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let y := (d.readBytes 64 32, d.readBytes 96 32)
    let o := BN_ADD x.1 x.2 y.1 y.2
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_ADD failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (false, ∅, ⟨0⟩, A, .empty)

private def bn_addOutput₀ :=
  let (_, _, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        inputData := x₁ ++ y₁ ++ x₂ ++ y₂
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  x₂ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₂ : ByteArray := UInt256.toByteArray ⟨2⟩

private def bn_addOutput₁ :=
  let (_, _, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv) with
        inputData := bn_addOutput₀ ++ x ++ y
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BN_MUL
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 6000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.inputData
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let n := d.readBytes 64 32
    let o := BN_MUL x.1 x.2 n
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_MUL failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (false, ∅, ⟨0⟩, A, .empty)

private def bn_mulOutput :=
  let (_, _, _, _, o) :=
    Ξ_BN_MUL
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv) with
        inputData := x₁ ++ y₁ ++ n
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨2⟩
  n  : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_SNARKV
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let k := d.size / 192
  let gᵣ : ℕ := 34000 * k + 45000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := SNARKV d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_SNARKV failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)

private def snarkvOutput :=
  let (_, _, _, _, o) :=
    Ξ_SNARKV
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv) with
        inputData := x ++ y ++ ffi.ByteArray.zeroes ⟨32 * 4⟩
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BLAKE2_F
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let gᵣ : ℕ := fromByteArrayBigEndian (d.extract 0 4)

  if g.toNat < gᵣ then
    dbg_trace "failed"
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := ffi.BLAKE2 d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BLAKE2_F failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)

def Ξ_PointEval
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (Bool × AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let gᵣ : ℕ := 50000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := PointEval d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_PointEval failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)
