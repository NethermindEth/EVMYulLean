import EvmYul.SharedState
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.Operations
import Mathlib.Data.List.Intervals

namespace EvmYul

namespace SharedState

section Keccak

-- def keccak256 (s : SharedState) (p n : UInt256) : Option (UInt256 × SharedState) :=
--   let interval : List UInt256 := mkInterval s.toMachineState p n
--   match s.keccakMap.find? interval with
--     | .some val => .some (val, s)
--     | .none     =>
--     match s.toState.keccakRange.partition (λ x ↦ x ∈ s.toState.usedRange) with
--       | (_,(r :: rs)) =>
--         .some (r, { s with toState.keccakMap := s.toState.keccakMap.insert interval r,
--                            toState.keccakRange := rs,
--                            toState.usedRange := s.toState.usedRange.insert r })
--       | (_, []) => .none
--   where mkInterval (ms : MachineState) (p n : UInt256) : List UInt256 :=
--     (List.Ico p (p + n)).map ms.lookupMemory

end Keccak

section Memory

def writeWord (self : SharedState) (addr v : UInt256) : SharedState :=
  { self with toMachineState := self.toMachineState.writeWord addr v }

def writeBytes (self : SharedState) (source : ByteArray) (s n : Nat) : SharedState :=
  { self with toMachineState := self.toMachineState.writeBytes source (.ofNat s) n }

def calldatacopy (self : SharedState) (mstart datastart size : UInt256) : SharedState :=
  let arr := self.toState.executionEnv.inputData.readBytes datastart.val size.val
  -- dbg_trace s!"{arr}"
  self.writeBytes arr mstart.toNat size.toNat

def codeCopy (self : SharedState) (mstart cstart size : UInt256) : SharedState :=
  let Ib := self.toState.executionEnv.code.readBytes cstart.val size.val -- TODO(double check, changed in a fast-and-loose manner)
  -- dbg_trace s!"code: {toHex Ib}"
  self.writeBytes Ib mstart.toNat size.toNat

-- def extCodeCopy (self : SharedState) (acc mstart cstart s : UInt256) : SharedState :=
--   dbg_trace s!"mstart: {mstart} cstart: {cstart} s: {s}"
--   let addr := Address.ofUInt256 acc
--   let sState' : SharedState :=
--     match self.toState.lookupAccount addr with
--     | .some act1 =>
--       let Ib := act1.code.extract' cstart.val s.val
--       (·.1) <| Ib.foldl (init := (self, mstart)) λ (sa, j) i ↦ (sa.writeWord j i.toUInt256, j + 1)
--     | _ =>
--       (·.1) <| s.val.fold (init := (self, mstart)) λ _ (sa , j) ↦ (sa.writeWord j 0, j + 1)
--   {sState' with toState.substate := .addAccessedAccount self.toState.substate addr}

/--
TODO - wrong?
-/
def extCodeCopy' (self : SharedState) (acc mstart cstart size : UInt256) : SharedState :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  if 2^16 < size then dbg_trace s!"TODO - extCodeCopy called on a state which does _not_ recognise the address {acc.toNat} and with too big size: {size}; currently, this fails silently"; self else
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.toState.lookupAccount addr |>.option .empty Account.code
  let b : ByteArray := b.readBytes cstart size
  let sState' := (self.writeBytes b mstart size)
  {sState' with toState.substate := .addAccessedAccount self.toState.substate addr}

end Memory

def logOp (μ₀ μ₁ : UInt256) (t : List UInt256) (sState : SharedState) : SharedState :=
    let Iₐ := sState.executionEnv.codeOwner
    let ⟨evmState, mState⟩ := sState
    let (mem, newMState) := mState.readBytes μ₀ μ₁.toNat
    let logSeries' := evmState.substate.logSeries.push (Iₐ, t, mem)
    {sState with substate.logSeries := logSeries', toMachineState := newMState}

end SharedState

end EvmYul
