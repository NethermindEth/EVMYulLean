import Mathlib.Data.Nat.Log

import EvmYul.EVM.State
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace EVM

/-
Appendix G. Fee Schedule
-/

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
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
def Csstore (s : EVM.State) : ℕ :=
  let { stack := μₛ, accountMap := σ, σ₀ := σ₀, executionEnv.codeOwner := Iₐ, .. } := s
  let { storage := σ_Iₐ, .. } := σ.find! Iₐ
  let storeAddr := μₛ[0]!
  let v₀ :=
    match σ₀.find? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.findD storeAddr ⟨0⟩
  let v := σ_Iₐ.findD storeAddr ⟨0⟩
  let v' := μₛ[1]!
  let loadComponent :=
    if s.substate.accessedStorageKeys.contains (Iₐ, storeAddr) then
      0
    else
      Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v             then Gwarmaccess else
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
  let { substate.accessedAccounts := Aₐ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let c_cold := if Aₐ.contains r then 0 else Gcoldaccountaccess
  let c_new :=
    if State.dead σ r ∧ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
      Gnewaccount
    else 0
  Gselfdestruct + c_cold + c_new

/--
NB Assumes stack coherency.
-/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) : ℕ :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

def Ctload : ℕ :=
  Gwarmaccess

/--
(331)
-/
def L (n : ℕ) : ℕ := n - (n / 64)

def Cnew (t : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) : ℕ :=
  if EvmYul.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

def Cxfer (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then Gcallvalue else 0

def Cextra (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  Caccess t A + Cxfer val + Cnew r val σ

def Cgascap (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) :=
  if μ.gasAvailable.toNat >= Cextra t r val σ A then
    min (L <| (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat
  else
    g.toNat

def Ccallgas (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  match val with
    | ⟨0⟩ => Cgascap t r val g σ μ A
    | _ => Cgascap t r val g σ μ A + GasConstants.Gcallstipend

/--
NB Assumes stack coherence.
-/
def Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  Cgascap t r val g σ μ A + Cextra t r val σ A

/--
(65)
-/
def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

def intrinsicGas (T : Transaction) : ℕ :=
  let g₀_data :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let g₀_create : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + R (T.base.data.size)
    else 0

  let g₀_accessList : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  g₀_data + g₀_create + GasConstants.Gtransaction + g₀_accessList

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
    | .EXTCODECOPY => Caccess (AccountAddress.ofUInt256 μₛ[0]!) A + Gcopy * ((μₛ[3]!.toNat + 31) / 32)
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
    | .CALL =>         Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .CALLCODE =>     Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner μₛ[2]! μₛ[0]! σ μ A
    | .DELEGATECALL => Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner    ⟨0⟩ μₛ[0]! σ μ A
    | .STATICCALL =>   Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!)    ⟨0⟩ μₛ[0]! σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then Gverylow + Gcopy * ((μₛ[2]!.toNat + 31) / 32) else
      if w ∈ Wextaccount then Caccess (AccountAddress.ofUInt256 μₛ[0]!) A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      0

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/

def memoryExpansionCost (s : EVM.State) (instr : Operation .EVM) : ℕ :=
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
        let m : ℕ := MachineState.M s.toMachineState.activeWords.toNat s.stack[3]!.toNat s.stack[4]!.toNat
        .ofNat <| MachineState.M m s.stack[5]!.toNat s.stack[6]!.toNat
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ:= MachineState.M s.toMachineState.activeWords.toNat s.stack[2]!.toNat s.stack[3]!.toNat
        .ofNat <| MachineState.M m s.stack[4]!.toNat s.stack[5]!.toNat
      | .RETURN | .REVERT => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | _ => s.toMachineState.activeWords

end Gas

end EVM

end EvmYul
