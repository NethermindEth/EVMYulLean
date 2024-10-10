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

open EvmYul

def Ξ_ECREC
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 := 3000

  if g < gᵣ then
    (∅, 0, A, .empty)
  else
    let d := I.inputData
    let h := d.readBytes 0 32
    let v := d.readBytes 32 32
    let r := d.readBytes 64 32
    let s := d.readBytes 96 32
    let v' : UInt256 := fromBytesBigEndian v.data.data
    let r' : UInt256 := fromBytesBigEndian r.data.data
    let s' : UInt256 := fromBytesBigEndian s.data.data
    let o :=
      match ECDSARECOVER h v r s with
        | .ok s =>
          if v' < 27 || 28 < v' || r' = 0 || r' >= secp256k1n || s' = 0 || s' >= secp256k1n then
            .empty
          else
            ByteArray.zeroes ⟨12⟩ ++ (KEC s).extract 12 32
        | .error e =>
          dbg_trace s!"Ξ_ECREC failed: {e}"
          .empty
    (σ, g - gᵣ, A, o)

def Ξ_SHA256
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 :=
    let l := I.inputData.size
    let rem := l % 32
    let divided := l / 32
    let ceil := if rem == 0 then divided else divided + 1
    60 + 12 * ceil

  if g < gᵣ then
    (∅, 0, A, .empty)
  else
    let o :=
      match SHA256 I.inputData with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_SHA56 failed: {e}"
          .empty
    (σ, g - gᵣ, A, o)

def Ξ_RIP160
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 :=
    let l := I.inputData.size
    let rem := l % 32
    let divided := l / 32
    let ceil := if rem == 0 then divided else divided + 1
    60 + 12 * ceil

  if g < gᵣ then
    (∅, 0, A, .empty)
  else
    let o :=
      match RIP160 I.inputData with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_RIP160 failed: {e}"
          .empty
    (σ, g - gᵣ, A, o)

def Ξ_ID
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 :=
    let l := I.inputData.size
    let rem := l % 32
    let divided := l / 32
    let ceil := if rem == 0 then divided else divided + 1
    15 + 3 * ceil

  if g < gᵣ then
    (∅, 0, A, .empty)
  else
    let o := I.inputData
    (σ, g - gᵣ, A, o)

def expModAux (m : ℕ) (a : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => a % m
  | n@(k + 1) =>
    if n % 2 == 1 then
      expModAux m (a * c % m) (c * c % m) (n / 2)
    else
      expModAux m (a % m)     (c * c % m) (n / 2)

def expMod (m : ℕ) (b : UInt256) (n : ℕ) : ℕ := expModAux m 1 b n

def Ξ_EXPMOD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let l_B := d.readBytes 0 32 |>.data.data |> fromBytesBigEndian
  let l_E := d.readBytes 32 32 |>.data.data |> fromBytesBigEndian
  let l_M := d.readBytes 64 32 |>.data.data |> fromBytesBigEndian
  let B := d.readBytes 96 l_B |>.data.data |> fromBytesBigEndian
  let E := d.readBytes (96 + l_B) l_E |>.data.data |> fromBytesBigEndian
  let M := d.readBytes (96 + l_B + l_E) l_M |>.data.data |> fromBytesBigEndian

  let l_E' :=
    let E_firstWord := d.readBytes (96 + l_B) 32 |>.data.data |> fromBytesBigEndian
    if l_E ≤ 32 && E == 0 then
      0
    else
      if l_E ≤ 32 && E != 0 then
        Nat.log 2 E
      else
        if 32 < l_E && E_firstWord != 0 then
          8 * (l_E - 32) + (Nat.log 2 E_firstWord)
        else
          8 * (l_E - 32)

  let gᵣ :=
    let G_quaddivisor := 3
    let f x :=
      let rem := x % 8
      let divided := x / 8
      let ceil := if rem == 0 then divided else divided + 1
      ceil ^ 2

    max 200 (f (max l_M l_B) * max l_E' 1 / G_quaddivisor)

  let o : ByteArray := BE (expMod M B E)
  let o : ByteArray := ByteArray.zeroes ⟨l_M - o.size⟩ ++ o

  (σ, g - gᵣ, A, o)

def Ξ_BN_ADD
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 := 150
  let d := I.inputData
  let x := (d.readBytes 0 32, d.readBytes 32 32)
  let y := (d.readBytes 64 32, d.readBytes 96 32)
  let o := BN_ADD x.1 x.2 y.1 y.2
  match o with
    | .ok o => (σ, g - gᵣ, A, o)
    | .error e =>
      dbg_trace s!"Ξ_BN_ADD failed: {e}"
      (σ, g - gᵣ, A, .empty)

def Ξ_BN_MUL
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let gᵣ : UInt256 := 6000
  let d := I.inputData
  let x := (d.readBytes 0 32, d.readBytes 32 32)
  let n := d.readBytes 64 32
  let o := BN_MUL x.1 x.2 n
  match o with
    | .ok o => (σ, g - gᵣ, A, o)
    | .error e =>
      dbg_trace s!"Ξ_BN_MUL failed: {e}"
      (σ, g - gᵣ, A, .empty)

def Ξ_SNARKV
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let k := d.size / 192
  let gᵣ : UInt256 := 34000 * k + 45000

  let o := SNARKV d
  match o with
    | .ok o => (σ, g - gᵣ, A, o)
    | .error e =>
      dbg_trace s!"Ξ_SNARKV failed: {e}"
      (∅, 0, A, .empty)

def Ξ_BLAKE2_F
  (σ : AccountMap)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  (AccountMap × UInt256 × Substate × ByteArray)
:=
  let d := I.inputData
  let k := d.size / 192
  let gᵣ : UInt256 := 34000 * k + 45000

  let o := BLAKE2_F d
  match o with
    | .ok o => (σ, g - gᵣ, A, o)
    | .error e =>
      dbg_trace s!"Ξ_BLAKE2_F failed: {e}"
      (∅, 0, A, .empty)
