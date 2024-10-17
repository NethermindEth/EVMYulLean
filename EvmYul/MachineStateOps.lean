import Batteries.Data.RBMap

import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

namespace EvmYul

namespace MachineState

section Memory

open Batteries (RBMap)

-- Apendix H, (320)
def M (s f l : ℕ) : ℕ :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    -- The addition is not subject to s²⁵⁶ division (at least that's what MSTORE suggests)
    let rem := (f + l) % 32
    let divided := (f + l) / 32
    max s (if rem == 0 then divided else divided + 1)

def newMax (self : MachineState) (addr : UInt256) (numOctets : ℕ) : ℕ :=
  M self.activeWords addr.1 numOctets

def x : ByteArray := "hello".toUTF8
def y : ByteArray := "kokusho".toUTF8

def writeBytes (self : MachineState) (source : ByteArray) (addr : UInt256) (size : ℕ) : MachineState :=
  -- dbg_trace "writeBytes"
  -- dbg_trace s!"current mem: {self.memory} source: {source} s: {s} n: {n}"
  let maxPracticalAddress := self.activeWordsWritten * 32
  let practicalSize₁ := min source.size size
  let practicalSize₂ : ℕ := maxPracticalAddress.val - (addr + practicalSize₁).val
  { self with
      memory :=
        self.memory.writeMemory
          source
          addr
          (practicalSize₁ + practicalSize₂)
      activeWords := self.newMax addr size
      activeWordsWritten := self.newMax addr practicalSize₁
  }

def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  self.writeBytes source addr numOctets

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

def readBytes (self : MachineState) (addr size : UInt256) : ByteArray × MachineState := -- dbg_trace s!"readBytes addr: {addr} size: {size}"
  let size :=
    if size > 2^35 then
      panic! s!"Can not handle reding byte arrays larger than 2^35 ({2^35})"
    else size
  let maxPracticalAddress := self.activeWordsWritten * 32
  let practicalLastAddr := min maxPracticalAddress (addr + size)
  let practicalSize : ℕ := practicalLastAddr.val - addr.val
  let bytes := self.memory.readMemory addr practicalSize ++ ByteArray.zeroes ⟨size.val - practicalSize⟩
  let newMachineState := { self with activeWords := self.newMax addr size}
  (bytes, newMachineState)

/--
TODO - Currently a debug version.

-- Failing at least `sha3_d0g0v0_Cancun` in
-- `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/sha3.json`.
-/
def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 × MachineState :=
  let (bytes, newMachineState) := self.readBytes addr 32
  let val := fromBytesBigEndian bytes.data.data
  (val, newMachineState)

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
  self.activeWords * 32

def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  self.lookupMemory spos

def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  self.writeWord spos sval

def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  self.writeBytes ⟨#[UInt8.ofNat sval]⟩ spos 1

def mcopy (self : MachineState) (mstart datastart s : UInt256) : MachineState :=
  let (arr, newMachineState) := self.readBytes datastart.val s.val
  newMachineState.writeBytes arr mstart s

def gas (self : MachineState) : UInt256 :=
  self.gasAvailable

end Memory

section ReturnData

def setReturnData (self : MachineState) (r : ByteArray) : MachineState :=
  { self with returnData := r }

def setHReturn (self : MachineState) (r : ByteArray) : MachineState :=
  { self with H_return := r }

def returndatasize (self : MachineState) : UInt256 :=
  self.returnData.size

def returndataat (self : MachineState) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.val 0

def returndatacopy (self : MachineState) (mstart rstart size : UInt256) : Option MachineState :=
  let pos := rstart.val + size.val
  -- TODO:
  -- "The additions in μₛ[1]+i are not subject to the 2^256 modulo"
  if UInt256.size ≤ pos || self.returndatasize.val < pos then .none
  else
    let rdata := self.returnData.readBytes rstart.val size.val
    self.writeBytes rdata mstart size

def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState := Id.run do
  let (bytes, newMachineState) := self.readBytes mstart.val s.val
  newMachineState.setHReturn bytes

def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  self.evmReturn mstart s

end ReturnData

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  -- dbg_trace s!"called keccak256; going to be looking up a lot of vals; s: {s}"
  let (bytes, newMachineState) := self.readBytes mstart.val s.val
  -- dbg_trace s!"got vals {vals}"
  let kec := KEC bytes
  -- dbg_trace s!"got kec {kec}"
  (fromBytesBigEndian kec.data.data, newMachineState)

section Gas

def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul
