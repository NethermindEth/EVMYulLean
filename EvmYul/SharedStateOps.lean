import EvmYul.SharedState
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.Operations
import Mathlib.Data.List.Intervals

namespace EvmYul

namespace SharedState

section Keccak

def keccak256 (s : SharedState) (p n : UInt256) : Option (UInt256 × SharedState) :=
  let interval : List UInt256 := mkInterval s.toMachineState p n
  match s.keccakMap.find? interval with
    | .some val => .some (val, s)
    | .none     =>
    match s.toState.keccakRange.partition (λ x ↦ x ∈ s.toState.usedRange) with
      | (_,(r :: rs)) =>
        .some (r, { s with toState.keccakMap := s.toState.keccakMap.insert interval r,
                           toState.keccakRange := rs,
                           toState.usedRange := s.toState.usedRange.insert r })
      | (_, []) => .none
  where mkInterval (ms : MachineState) (p n : UInt256) : List UInt256 :=
    (List.Ico p (p + n)).map ms.lookupMemory

end Keccak

section Memory

def updateMemory (self : SharedState) (addr v : UInt256) (numOctets : WordSize := WordSize.Standard) : SharedState :=
  { self with toMachineState := self.toMachineState.updateMemory addr v numOctets }

def copyMemory (self : SharedState) (source : ByteArray) (s n : Nat) : SharedState :=
  { self with toMachineState := self.toMachineState.copyMemory source s n }

def calldatacopy (self : SharedState) (mstart datastart s : UInt256) : SharedState :=
  let arr := self.toState.executionEnv.inputData.extract' datastart.val s.val
  -- dbg_trace s!"{arr}"
  (·.1) <| arr.foldl (init := (self, mstart)) λ (sa , j) i ↦ (sa.updateMemory j i.val, j + 1)

def big : UInt256 := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa

def codeCopy (self : SharedState) (mstart cstart s : UInt256) : SharedState :=
  let Ib := self.toState.executionEnv.code.extract' cstart.val s.val -- TODO(double check, changed in a fast-and-loose manner)
  (·.1) <| Ib.foldl (init := (self, mstart)) λ (sa, j) i ↦ (sa.updateMemory j i.toUInt256, j + 1)

-- def extCodeCopy (self : SharedState) (acc mstart cstart s : UInt256) : SharedState :=
--   dbg_trace s!"mstart: {mstart} cstart: {cstart} s: {s}"
--   let addr := Address.ofUInt256 acc
--   let sState' : SharedState :=
--     match self.toState.lookupAccount addr with
--     | .some act1 =>
--       let Ib := act1.code.extract' cstart.val s.val
--       (·.1) <| Ib.foldl (init := (self, mstart)) λ (sa, j) i ↦ (sa.updateMemory j i.toUInt256, j + 1)
--     | _ =>
--       (·.1) <| s.val.fold (init := (self, mstart)) λ _ (sa , j) ↦ (sa.updateMemory j 0, j + 1)
--   {sState' with toState.substate := .addAccessedAccount self.toState.substate addr}

/--
TODO - wrong
-/
def extCodeCopy' (self : SharedState) (acc mstart cstart s : UInt256) : SharedState :=
  if 2^16 < s then dbg_trace s!"TODO - extCodeCopy called on a state which does _not_ recognise the address {acc} and with too big size: {s}; currently, this fails silently"; self else
  let addr := Address.ofUInt256 acc
  let sState' : SharedState :=
    match self.toState.lookupAccount addr with
    | .some act1 =>
      let Ib := act1.code.extract' cstart.val s.val
      self.copyMemory Ib mstart s
    | _ => let zeroes := Array.mkArray s 0
           self.copyMemory ⟨zeroes⟩ mstart s
          -- TODO - Probably a bug, although zeroes need copying (I think?) so maybe we can address it somehow elsewhere 
           -- Might need to write some FFI for this; need an array of 2^160 bytes that does not crash Lean.
  {sState' with toState.substate := .addAccessedAccount self.toState.substate addr}

end Memory

def logOp (μ₀ μ₁ : UInt256) (t : List UInt256) (sState : SharedState) : Substate × UInt256 :=
    let Iₐ := sState.executionEnv.codeOwner
    let mem := sState.toMachineState.lookupMemoryRange μ₀ μ₁
    let logSeries' := sState.toState.substate.logSeries.push (Iₐ, t, mem)
    let μᵢ' := MachineState.M sState.maxAddress μ₀ μ₁
    ({sState.substate with logSeries := logSeries'}, μᵢ')

end SharedState

end EvmYul
