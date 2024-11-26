import EvmYul.EVM.State
import EvmYul.StateOps
import EvmYul.MachineStateOps

namespace EvmYul

namespace EVM

/-
Appendix G. Fee Schedule
-/

namespace GasConstants

section FeeSchedule

def Gzero : ℕ              := 0
def Gjumpdest : ℕ          := 1
def Gbase : ℕ              := 2
def Gverylow : ℕ           := 3
def Glow : ℕ               := 5
def Gmid : ℕ               := 8
def Ghigh : ℕ              := 10
def Gwarmaccess : ℕ        := 100
def Gaccesslistaddress : ℕ := 2400
def Gaccessliststorage : ℕ := 1900
def Gcoldaccountaccess : ℕ := 2600
def Gcoldsload : ℕ         := 2100
def Gsset : ℕ              := 20000
def Gsreset : ℕ            := 2900
def Rsclear : ℕ            := 4800
def Gselfdestruct : ℕ      := 5000
def Gcreate : ℕ            := 32000
def Gcodedeposit : ℕ       := 200
def Ginitcodeword : ℕ      := 2
def Gcallvalue : ℕ         := 9000
def Gcallstipend : ℕ       := 2300
def Gnewaccount : ℕ        := 25000
def Gexp : ℕ               := 10
def Gexpbyte : ℕ           := 50
def Gmemory : ℕ            := 3
def Gtxcreate : ℕ          := 32000
def Gtxdatazero : ℕ        := 4
def Gtxdatanonzero : ℕ     := 16
def Gtransaction : ℕ       := 21000
def Glog : ℕ               := 375
def Glogdata : ℕ           := 8
def Glogtopic : ℕ          := 375
def Gkeccak256 : ℕ         := 30
def Gkeccak256word : ℕ     := 6
def Gcopy : ℕ              := 3
def Gblockhash : ℕ         := 20
def HASH_OPCODE_GAS : ℕ    := 3

end FeeSchedule

end GasConstants

namespace InstructionGasGroups

def Wzero : List (Operation .EVM) := [.STOP, .RETURN, .REVERT]

def Wbase : List (Operation .EVM) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .BLOBBASEFEE, .PUSH0]

def Wverylow : List (Operation .EVM) := [
  .ADD, .SUB, .NOT, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR,
  .CALLDATALOAD, .MLOAD, .MSTORE, .MSTORE8
  ] ++ pushInstrsWithoutZero
    ++ dupInstrs
    ++ swapInstrs
  where
    pushInstrsWithoutZero : List (Operation .EVM) := [
      .PUSH1, .PUSH2, .PUSH3, .PUSH4, .PUSH5,
      .PUSH6, .PUSH7, .PUSH8, .PUSH9, .PUSH10,
      .PUSH11, .PUSH12, .PUSH13, .PUSH14, .PUSH15,
      .PUSH16, .PUSH17, .PUSH18, .PUSH19, .PUSH20,
      .PUSH21, .PUSH22, .PUSH23, .PUSH24, .PUSH25,
      .PUSH26, .PUSH27, .PUSH28, .PUSH29, .PUSH30,
      .PUSH31, .PUSH32
    ]
    dupInstrs : List (Operation .EVM) := [
      .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
      .DUP6, .DUP7, .DUP8, .DUP9, .DUP10,
      .DUP11, .DUP12, .DUP13, .DUP14, .DUP15,
      .DUP16
    ]
    swapInstrs : List (Operation .EVM) := [
      .SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5,
      .SWAP6, .SWAP7, .SWAP8, .SWAP9, .SWAP10,
      .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15,
      .SWAP16
    ]

def Wlow : List (Operation .EVM) := [
  .MUL, .DIV, .SDIV, .MOD, .SMOD, .SIGNEXTEND, .SELFBALANCE
]

def Wmid : List (Operation .EVM) := [
  .ADDMOD, .MULMOD, .JUMP
]

def Whigh : List (Operation .EVM) := [
  .JUMPI
]

def Wcopy : List (Operation .EVM) := [
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY
]

def Wcall : List (Operation .EVM) := [
  .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL
]

def Wextaccount : List (Operation .EVM) := [
  .BALANCE, .EXTCODESIZE, .EXTCODEHASH
]

end InstructionGasGroups

section Gas

open GasConstants InstructionGasGroups

/--
(328)
-/
def Cₘ (a : UInt256) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient) -- TODO(check) - What is subject to `% 2^256` here?
                                                                                --               Note that the YP takes an explicit floor, we have division in Nat.
  where QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
def Csstore (s : EVM.State) : ℕ :=
  let { stack := μₛ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  -- SSTORE should handle missing Iₐ
  let { storage := σ, ostorage := σ₀, .. } := σ.find! Iₐ
  let storeAddr := μₛ[0]!
  let v₀ := σ₀.findD storeAddr ⟨0⟩
  let v := σ.findD storeAddr ⟨0⟩
  let v' := μₛ[1]!
  let loadComponent := if s.substate.accessedStorageKeys.contains (Iₐ, storeAddr) then 0 else Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v           then Gwarmaccess else
                        if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else
                        /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  loadComponent + storeComponent

def Ctstore : ℕ :=
  let loadComponent := 0
  let storeComponent := Gwarmaccess
  loadComponent + storeComponent

/--
(328)
-/
def Caccess (a : AccountAddress) (A : Substate) : ℕ :=
  if A.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

/--
CHECK -
In YP we have `Cselfdestruct(σ, μ)`; if we were to compute `Aₐ` that we need, we would need an
address in `σ` - is this address supposed to be obvious?
CURRENT SOLUTION -
We take `EVM.State`.
-/
def Cselfdestruct (s : EVM.State) : ℕ :=
  let r := AccountAddress.ofUInt256 s.stack[0]!
  let { substate.accessedAccounts := Aₐ, .. } := s
  if Aₐ.contains r then 0 else Gcoldaccountaccess

/--
NB Assumes stack coherency.
-/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv) : ℕ :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

def Ctload : ℕ :=
  Gwarmaccess

/--
(331)
-/
def L (n : ℕ) : ℕ := n - (n / 64)

def Cnew (t : AccountAddress) (val : UInt256) (σ : AccountMap) : ℕ :=
  if EvmYul.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

def Cxfer (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then Gcallvalue else 0

def Cextra (t : AccountAddress) (val : UInt256) (σ : AccountMap) (A : Substate) : ℕ :=
  Caccess t A + Cxfer val + Cnew t val σ

def Cgascap (t : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) :=
  if μ.gasAvailable.toNat >= Cextra t val σ A then
    -- dbg_trace s!"gasAvailable {μ.gasAvailable} >= Cextra {Cextra t val σ A}"
    min (L <| (μ.gasAvailable.toNat - Cextra t val σ A)) g.toNat
  else
    -- dbg_trace s!"gasAvailable {μ.gasAvailable} < Cextra {Cextra t val σ A}"
    g.toNat

def Ccallgas (t : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) : ℕ :=
  match val with
    | ⟨0⟩ => Cgascap t val g σ μ A
    | _ => Cgascap t val g σ μ A + GasConstants.Gcallstipend

/--
NB Assumes stack coherence.
-/
def Ccall (t : AccountAddress) (val g : UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) : ℕ :=
  -- dbg_trace s!"Ccall: {Cgascap t val g σ μ A} + {Cextra t val σ A}"
  Cgascap t val g σ μ A + Cextra t val σ A

/--
(65)
-/
def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

/--
H.1. Gas Cost - the third summand.

NB Stack accesses are assumed guarded here and we access with `!`.
This is for keeping in sync with the way the YP is structures, at least for the time being.
-/
def C' (s : State) (instr : Operation .EVM) : ℕ :=
  let { accountMap := σ, stack := μₛ, substate := A, toMachineState := μ, executionEnv := I, ..} := s
  match instr with
    | .SSTORE => Csstore s
    | .TSTORE => Ctstore
    | .EXP => let μ₁ := μₛ[1]!; if μ₁ == ⟨0⟩ then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 μ₁.toNat) -- TODO(check) I think this floors by itself. cf. H.1. YP.
    | .EXTCODECOPY => Caccess (AccountAddress.ofUInt256 μₛ[0]!) A
    | .LOG0 => Glog + Glogdata * μₛ[1]!.toNat
    | .LOG1 => Glog + Glogdata * μₛ[1]!.toNat +     Glogtopic
    | .LOG2 => Glog + Glogdata * μₛ[1]!.toNat + 2 * Glogtopic
    | .LOG3 => Glog + Glogdata * μₛ[1]!.toNat + 3 * Glogtopic
    | .LOG4 => Glog + Glogdata * μₛ[1]!.toNat + 4 * Glogtopic
    | .SELFDESTRUCT => Cselfdestruct s
    | .CREATE => Gcreate + R μₛ[2]!.toNat
    | .CREATE2 => let μ₂ := μₛ[2]!; Gcreate + Gkeccak256word * ((μ₂.toNat + 31) / 32) + R μ₂.toNat
    | .KECCAK256 => Gkeccak256 + Gkeccak256word * ((μₛ[1]!.toNat + 31) / 32)
    | .JUMPDEST => Gjumpdest
    | .SLOAD => Csload μₛ A I
    | .TLOAD => Ctload
    | .BLOCKHASH => Gblockhash
    /-
      By `μₛ[2]` the YP means the value that is to be transferred,
      not what happens to be on the stack at index 2. Therefore it is 0 for
      `DELEGATECALL` and `STATICCALL`.
    -/
    | .CALL => Ccall (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .CALLCODE => Ccall (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .DELEGATECALL => Ccall (AccountAddress.ofUInt256 μₛ[1]!) ⟨0⟩ μₛ[0]! σ μ A
    | .STATICCALL   => Ccall (AccountAddress.ofUInt256 μₛ[1]!) ⟨0⟩ μₛ[0]! σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then Gverylow + Gcopy * ((μₛ[2]!.toNat + 31) / 32) else
      if w ∈ Wextaccount then Caccess (AccountAddress.ofUInt256 μₛ[0]!) A else
      -- if w ∈ Wcall then Ccall μₛ σ μ A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      dbg_trace s!"TODO - C called with an unknown instruction: {w.pretty}"; 0

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/
-- def C (s : EVM.State) (μ'ᵢ : UInt256) (instr : Operation .EVM) : Except EVM.Exception ℕ := do
--   let { toMachineState := μ, ..} := s
--   pure <| Cₘ μ'ᵢ - Cₘ μ.activeWords + (← C' s instr)


def memoryExpansionCost (s : EVM.State) (instr : Operation .EVM) : ℕ :=
  -- let { toMachineState := μ, ..} := s
  -- dbg_trace s!"{Cₘ μᵢ'} - {Cₘ s.toMachineState.activeWords} + {C' s instr}"
  Cₘ μᵢ' - Cₘ s.toMachineState.activeWords
 where
  μᵢ' : UInt256 :=
    match instr with
      | .KECCAK256 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CALLDATACOPY | .CODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MCOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat (max s.stack[0]!.toNat s.stack[1]!.toNat) s.stack[2]!.toNat
      | .EXTCODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[3]!.toNat
      | .RETURNDATACOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MLOAD | .MSTORE => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 32
      | .MSTORE8 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 1
      | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
        .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CREATE | .CREATE2 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[2]!.toNat
      | .CALL | .CALLCODE =>
        let m : ℕ:= MachineState.M s.toMachineState.activeWords.toNat s.stack[3]!.toNat s.stack[4]!.toNat
        .ofNat <| MachineState.M m s.stack[5]!.toNat s.stack[6]!.toNat
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ:= MachineState.M s.toMachineState.activeWords.toNat s.stack[2]!.toNat s.stack[3]!.toNat
        .ofNat <| MachineState.M m s.stack[4]!.toNat s.stack[5]!.toNat
      | .RETURN | .REVERT => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | _ => s.toMachineState.activeWords

end Gas

end EVM

end EvmYul
