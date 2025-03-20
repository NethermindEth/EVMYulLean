import Batteries.Data.RBMap

import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

namespace EvmYul

def writeBytes
  (source : ByteArray)
  (sourceAddr : ℕ)
  (self : MachineState)
  (destAddr len : ℕ)
 : MachineState :=
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

def x : ByteArray := "hello".toUTF8
def y : ByteArray := "kokusho".toUTF8

def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  writeBytes source 0 self addr.toNat numOctets

def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩ then ⟨0⟩ else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

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
  let self := writeBytes self.returnData rstart.toNat self mstart.toNat size.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }


def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
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
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  let kec := ffi.KEC bytes
  let newMachineState :=
    { self with activeWords := .ofNat (M self.activeWords.toNat mstart.toNat s.toNat) }
  (.ofNat (fromByteArrayBigEndian kec), newMachineState)

section Gas

def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := .ofNat gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul
