import Batteries.Data.RBMap

import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

namespace EvmYul

namespace MachineState

section Memory

open Batteries (RBMap)

def newMax (self : MachineState) (addr : UInt256) (numOctets : WordSize) : ℕ :=
  max self.maxAddress (Rat.ceil ((addr.1 + numOctets) / 32)).toNat

-- def updateMemory (self : MachineState) (addr v : UInt256) (numOctets : WordSize := WordSize.Standard) : MachineState :=
--   { self with memory := let addrs   := List.range 32 |>.map (·+addr)
--                         let inserts := addrs.zipWith (λ k v m ↦ RBMap.insert m k v) (toBytes! v)
--                         inserts.foldl (flip id) self.memory
--               maxAddress := self.newMax addr numOctets }

def x : ByteArray := "hello".toUTF8
def y : ByteArray := "kokusho".toUTF8

def updateMemory (self : MachineState) (addr v : UInt256) (numOctets : WordSize := WordSize.Standard) : MachineState :=
  -- dbg_trace "updateMemory"
  { self with memory := ByteArray.copySlice' (src     := ⟨⟨toBytes! v⟩⟩)
                                            (srcOff  := 0)
                                            (dest    := self.memory)
                                            (destOff := addr)
                                            (len     := numOctets) -- TODO - this will need an interface a'la `ByteArray.extract'`.
              maxAddress := self.newMax addr numOctets }

def copyMemory (self : MachineState) (source : ByteArray) (s n : Nat) : MachineState :=
  -- dbg_trace "copyMemory"
  -- dbg_trace s!"current mem: {self.memory} source: {source} s: {s} n: {n}"
  { self with memory := ByteArray.copySlice' (src     := source)
                                            (srcOff  := 0)
                                            (dest    := self.memory)
                                            (destOff := s)
                                            (len     := n)
              maxAddress := self.newMax (s + n) WordSize.Standard
  }

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

/--
TODO - Currently a debug version.

-- Failing at least `sha3_d0g0v0_Cancun` in
-- `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/sha3.json`.
-/
def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  fromBytes! (self.memory.extract' addr (addr + 32) |>.data.toList)

-- /--
-- TODO - Currently a debug version.
-- -/
-- def lookupMemoryRange (self : MachineState) (addr size : UInt256) : ByteArray := dbg_trace s!"lookupMemoryRange addr: {addr} size: {size}"
--   -- ⟨⟨List.map (λ i ↦ (self.memory.lookup (addr + i)).get!) (List.range size)⟩⟩
--   ⟨⟨List.range size |>.map λ i ↦ self.memory.findD (addr + i) 0⟩⟩

/--
TODO - Currently a debug version.
-/
def lookupMemoryRange (self : MachineState) (addr size : UInt256) : ByteArray := -- dbg_trace s!"lookupMemoryRange addr: {addr} size: {size}"
  self.memory.extract' addr (addr + size)

-- def lookupMemoryRange' (self : MachineState) (addr size : UInt256) : ByteArray := Id.run do
--   let mut result : ByteArray := ∅
--   let mut i := 0
--   while i < size do
--     dbg_trace s!"i: {i}"
--     result := result.push <| self.memory.findD (addr + i) 0
--     i := i + 1
--   return result

-- private def lookupMemoryRange''_aux (self : MachineState) (addr : UInt256) (res : ByteArray) : UInt256 → ByteArray
--   | 0 => res
--   | ⟨k + 1, _⟩ => lookupMemoryRange''_aux self addr (res.push <| self.memory.findD (addr + k) 0) k
-- termination_by k => k
-- decreasing_by {
--   simp_wf; simp [Fin.lt_def]
--   rw [Nat.mod_eq_of_lt] <;> omega
-- }

-- def lookupMemoryRange'' (self : MachineState) (addr size : UInt256) : ByteArray :=
--   lookupMemoryRange''_aux self addr .empty size

def msize (self : MachineState) : UInt256 :=
  self.maxAddress

def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := self.lookupMemory spos
  let rem := (spos + 32) % 32
  let divided := (spos + 32) / 32
  let maxAddress' := max self.maxAddress (if rem == 0 then divided else divided + 1)
  (val, {self with maxAddress := maxAddress'})

def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  self.updateMemory spos sval

def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  self.updateMemory spos (Fin.ofNat (sval.val % (2^8)))

def mcopy (self : MachineState) (mstart datastart s : UInt256) : MachineState :=
  let arr := self.lookupMemoryRange datastart.val s.val
  (·.1) <| arr.foldl (init := (self, mstart)) λ (sa , j) i ↦ (sa.updateMemory j i.val, j + 1)

def gas (self : MachineState) : UInt256 :=
  self.gasAvailable

-- Apendix H, (320)
def M (s f l : UInt256) : UInt256 :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    let rem := (f + l) % 32
    let divided := (f + l) / 32
    max s (if rem == 0 then divided else divided + 1)

end Memory

section ReturnData

def setReturnData (self : MachineState) (r : ByteArray) : MachineState :=
  { self with returnData := r }

def returndatasize (self : MachineState) : UInt256 :=
  self.returnData.size

def returndataat (self : MachineState) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.val 0

def returndatacopy (self : MachineState) (mstart rstart s : UInt256) : Option MachineState :=
  let pos := rstart.val + s.val
  -- TODO:
  -- "The additions in μₛ[1]+i are not subject to the 2^256 modulo"
  if UInt256.size ≤ pos || self.returndatasize.val ≤ pos then .none
  else
    let arr := self.returnData
    let rdata := arr.extract' rstart.val (rstart.val + s.val - 1)
    let s := rdata.data.foldr (init := (self , mstart))
                              λ v (ac, p) ↦ (ac.updateMemory p v.val, p +1)
    .some s.1

def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
  let vals := self.returnData.extract' mstart.val s.val
  let maxAddress' := M self.maxAddress mstart s
  {self with maxAddress := maxAddress'}.setReturnData vals

def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  self.evmReturn mstart s

end ReturnData

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  -- dbg_trace s!"called keccak256; going to be looking up a lot of vals; s: {s}"
  let vals := self.lookupMemoryRange mstart.val s.val
  -- dbg_trace s!"got vals {vals}"
  let kec := KEC vals
  -- dbg_trace s!"got kec {kec}"
  let maxAddress' := M self.maxAddress mstart s
  (fromBytesBigEndian kec.data.data, {self with maxAddress := maxAddress'})

section Gas

def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul
