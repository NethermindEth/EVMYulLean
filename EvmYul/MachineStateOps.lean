import Batteries.Data.RBMap

import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

-- import EvmYul.EVM.Gas

namespace EvmYul

def writeBytes
  (source : ByteArray)
  (sourceAddr : ℕ)
  (self : MachineState)
  (destAddr len : ℕ)
 : MachineState :=
  -- dbg_trace "writeBytes"
  -- dbg_trace s!"current mem: {self.memory} source: {source} s: {s} n: {n}"
  { self with
      memory := source.write sourceAddr self.memory destAddr len
  }

namespace MachineState

open Batteries (RBMap)

-- Appendix H, (320)
def M (s f l : ℕ) : ℕ :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    -- The addition is not subject to s²⁵⁶ division (at least that's what MSTORE suggests)
    max s ((f + l + 31) / 32)

-- def newMax (self : MachineState) (addr : UInt256) (numOctets : ℕ) : ℕ :=
--   M self.activeWords.toNat addr.1 numOctets

def x : ByteArray := "hello".toUTF8
def y : ByteArray := "kokusho".toUTF8

def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  writeBytes source 0 self addr.toNat numOctets

-- /--
-- TODO - Currently a debug version.

-- -- Failing at least `sha3_d0g0v0_Cancun` in
-- -- `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/sha3.json`.
-- -/
-- def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
--   -- fromBytes! (List.map (λ i ↦ (self.memory.lookup (addr + i)).get!) (List.range 32))

--   -- fromBytes! <| List.range 32 |>.map λ i ↦ self.memory.lookup (addr + i) |>.getD 0

--   fromBytes! <| List.range 32 |>.map λ i ↦
--     match self.memory.find? (addr + i) with
--       | .none => dbg_trace "lookup failed; addr: {addr} - returning 0"; 0
--       | .some val => val

-- def readBytes (self : MachineState) (addr : UInt256) (size : ℕ) : ByteArray × MachineState := -- dbg_trace s!"readBytes addr: {addr} size: {size}"
--   let size :=
--     if size > 2^35 then
--       panic! s!"Can not handle reading byte arrays larger than 2^35 ({2^35})"
--     else size
--   let bytes := self.memory.readMemory addr.toNat size
--   (bytes, self)

/--
TODO - Currently a debug version.

-- Failing at least `sha3_d0g0v0_Cancun` in
-- `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/sha3.json`.
-/
def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩ then ⟨0⟩ else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromBytesBigEndian bytes.data.data
    .ofNat val

-- /--
-- TODO - Currently a debug version.
-- -/
-- def readBytes (self : MachineState) (addr size : UInt256) : ByteArray := dbg_trace s!"readBytes addr: {addr} size: {size}"
--   -- ⟨⟨List.map (λ i ↦ (self.memory.lookup (addr + i)).get!) (List.range size)⟩⟩
--   ⟨⟨List.range size |>.map λ i ↦ self.memory.findD (addr + i) 0⟩⟩

-- def readBytes' (self : MachineState) (addr size : UInt256) : ByteArray := Id.run do
--   let mut result : ByteArray := ∅
--   let mut i := 0
--   while i < size do
--     dbg_trace s!"i: {i}"
--     result := result.push <| self.memory.findD (addr + i) 0
--     i := i + 1
--   return result

-- private def readBytes''_aux (self : MachineState) (addr : UInt256) (res : ByteArray) : UInt256 → ByteArray
--   | 0 => res
--   | ⟨k + 1, _⟩ => readBytes''_aux self addr (res.push <| self.memory.findD (addr + k) 0) k
-- termination_by k => k
-- decreasing_by {
--   simp_wf; simp [Fin.lt_def]
--   rw [Nat.mod_eq_of_lt] <;> omega
-- }

-- def readBytes'' (self : MachineState) (addr size : UInt256) : ByteArray :=
--   readBytes''_aux self addr .empty size

def msize (self : MachineState) : UInt256 :=
  self.activeWords * ⟨32⟩

def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := self.lookupMemory spos
  let self :=
    { self with
      activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
    }
  (val, self)

def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := self.writeWord spos sval
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
  }

def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := writeBytes ⟨#[UInt8.ofNat sval.toNat]⟩ 0 self spos.toNat 1
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 1)
  }

def mcopy (self : MachineState) (writeStart readStart s : UInt256) : MachineState :=
  -- let (arr, _) := self.readBytes readStart s.toNat
  let self := writeBytes self.memory readStart.toNat self writeStart.toNat s.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat (max writeStart.toNat readStart.toNat) s.toNat)
  }

def gas (self : MachineState) : UInt256 :=
  self.gasAvailable

section ReturnData

def setReturnData (self : MachineState) (r : ByteArray) : MachineState :=
  { self with returnData := r }

def setHReturn (self : MachineState) (r : ByteArray) : MachineState :=
  { self with H_return := r }

def returndatasize (self : MachineState) : UInt256 :=
  .ofNat self.returnData.size

def returndataat (self : MachineState) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.toNat 0

def returndatacopy (self : MachineState) (mstart rstart size : UInt256) : MachineState :=
  -- let pos := rstart.toNat + size.toNat
  -- TODO:
  -- "The additions in μₛ[1]+i are not subject to the 2^256 modulo"
  -- if UInt256.size ≤ pos || self.returndatasize.toNat < pos then .none
  -- else
  -- let rdata := self.returnData.readBytes rstart.toNat size.toNat
  let self := writeBytes self.returnData rstart.toNat self mstart.toNat size.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }


def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
  -- let (bytes, _) := self.readBytes mstart s.toNat
  -- let self := self.setHReturn bytes
  { self with
    H_return := self.memory.readWithPadding mstart.toNat s.toNat
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  let self := self.evmReturn mstart s
  { self with
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

end ReturnData

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  -- dbg_trace s!"called keccak256; going to be looking up a lot of vals; s: {s}"
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  -- dbg_trace s!"got vals {vals}"
  let kec := KEC bytes
  -- dbg_trace s!"got kec {kec}"
  let newMachineState :=
    { self with activeWords := .ofNat (M self.activeWords.toNat mstart.toNat s.toNat) }
  (.ofNat (fromBytesBigEndian kec.data.data), newMachineState)

section Gas

def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := .ofNat gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul
