import EvmYul.SharedState
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.MachineState
import EvmYul.Operations
import Mathlib.Data.List.Intervals

namespace EvmYul

namespace SharedState

section Keccak

end Keccak

section Memory

def writeWord {τ} (self : SharedState τ) (addr v : UInt256) : SharedState τ :=
  { self with toMachineState := self.toMachineState.writeWord addr v }


def calldatacopy {τ} (self : SharedState τ) (mstart datastart size : UInt256) : SharedState τ :=
  { self with
    memory := self.executionEnv.inputData.write datastart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def codeCopy  (self : SharedState .EVM) (mstart cstart size : UInt256) : SharedState .EVM :=
  { self with
    memory := self.executionEnv.code.write cstart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def extCodeCopy' (self : SharedState .EVM) (acc mstart cstart size : UInt256) : SharedState .EVM :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.toState.lookupAccount addr |>.option .empty (·.code)
  { self with
    memory := b.write cstart self.memory mstart size
    substate := .addAccessedAccount self.toState.substate addr
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart size)
  }

end Memory

def logOp {τ} (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : SharedState τ) : SharedState τ :=
  let Iₐ := sState.executionEnv.codeOwner
  let mem := sState.memory.readWithPadding μ₀.toNat μ₁.toNat
  { sState with
    substate.logSeries := sState.substate.logSeries.push ⟨Iₐ, t, mem⟩
    activeWords := .ofNat (MachineState.M sState.activeWords.toNat μ₀.toNat μ₁.toNat)
  }

end SharedState

end EvmYul
