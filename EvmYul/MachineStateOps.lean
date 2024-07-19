import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

namespace EvmYul

namespace MachineState

section Memory

def new_max (self : MachineState) (addr : UInt256) (numOctets : WordSize) : ℕ :=
  max self.maxAddress (Rat.ceil ((addr.1 + numOctets) / 32)).toNat

def updateMemory (self : MachineState) (addr v : UInt256) (numOctets : WordSize := WordSize.Standard) : MachineState :=
  { self with memory := let addrs   := List.range 32 |>.map (·+addr)
                        let inserts := addrs.zipWith Finmap.insert (toBytes! v)
                        inserts.foldl (init := self.memory) (flip id)
              maxAddress := self.new_max addr numOctets }

def copyMemory (self : MachineState) (source : ByteArray) (s n : Nat) : MachineState :=
  { self with memory := (List.range n).map (UInt256.ofNat) |>.foldl (init := self.memory)
                          λ mem addr ↦ mem.insert (addr+s) (source.get! addr)
              maxAddress := self.new_max (s + n) WordSize.Standard
  }

def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  fromBytes! (List.map (λ i ↦ (self.memory.lookup (addr + i)).get!) (List.range 32))

def lookupMemoryRange (self : MachineState) (addr size : UInt256) : ByteArray :=
  ⟨⟨List.map (λ i ↦ (self.memory.lookup (addr + i)).get!) (List.range size)⟩⟩

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
    let rdata := arr.extract rstart.val (rstart.val + s.val - 1)
    let s := rdata.data.foldr (init := (self , mstart))
                              λ v (ac, p) ↦ (ac.updateMemory p v.val, p +1)
    .some s.1

def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
  let vals := self.returnData.extract mstart.val s.val
  let maxAddress' := M self.maxAddress mstart s
  {self with maxAddress := maxAddress'}.setReturnData vals

def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  self.evmReturn mstart s

end ReturnData

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  let vals := self.lookupMemoryRange mstart.val s.val
  let kec := KEC vals
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
