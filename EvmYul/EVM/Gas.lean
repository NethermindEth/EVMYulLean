import EvmYul.Maps.YPState
import EvmYul.MachineState
import EvmYul.State.Substate
import EvmYul.State.ExecutionEnv
import EvmYul.EVM.Exception
import EvmYul.StateOps

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

end FeeSchedule

end GasConstants

namespace InstructionGasGroups

def Wzero : List (Operation .EVM) := [.STOP, .RETURN, .REVERT]

def Wbase : List (Operation .EVM) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .PUSH0]

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
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY
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
def Cₘ(a : UInt256) : UInt256 := Gmemory * a + ((a * a) / QuadraticCeofficient) -- TODO(check) - What is subject to `% 2^256` here?
                                                                                --               Note that the YP takes an explicit floor, we have division in Nat.
  where QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
def Csstore (s : State) : Except EVM.Exception UInt256 := do
  let { stack := μₛ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let .some { storage := σ, ostorage := σ₀, .. } := σ.find? Iₐ | throw .SenderMustExist
  let storeAddr := μₛ[0]!
  let v₀ := σ₀.findD storeAddr 0
  let v := σ.findD storeAddr 0
  let v' := μₛ[1]!
  let loadComponent := if s.substate.accessedStorageKeys.contains (Iₐ, storeAddr) then 0 else Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v           then Gwarmaccess else
                        if v ≠ v' && v₀ = v && v₀ = 0 then Gsset else
                        /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  pure <| loadComponent + storeComponent

/--
(328)
-/
def Caccess (a : Address) (A : Substate) : UInt256 :=
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
def Cselfdestruct (s : EVM.State) : UInt256 :=
  let r := Address.ofUInt256 s.stack[0]!
  let { substate.accessedAccounts := Aₐ, .. } := s
  if Aₐ.contains r then 0 else Gcoldaccountaccess

/--
NB Assumes stack coherency.
-/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv) : UInt256 :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

/--
(331)
-/
def L (n : UInt256) := n.val - (n.val / 64)

/--
NB Assumes stack coherence.
-/
def Ccall (μₛ : Stack UInt256) (σ : AccountMap) (μ : MachineState) (A : Substate) : UInt256 :=
  Cgascap σ μ μₛ A + Cextra σ μₛ A
  where
    /-
    NB Slightly redundant as we could reference the `Ccall` parameters directly,
       but this is a bit closer to the YP for now.
    -/
    t := Address.ofUInt256 μₛ[1]!

    Cnew (σ : AccountMap) (μₛ : Stack UInt256) :=
      if EvmYul.State.dead σ t && μₛ[2]! != 0 then Gnewaccount else 0

    Cxfer (μₛ : Stack UInt256) :=
      if μₛ[2]! != 0 then Gcallvalue else 0

    Cextra (σ : AccountMap) (μₛ : Stack UInt256) (A : Substate) :=
      Caccess t A + Cxfer μₛ + Cnew σ μₛ

    Cgascap (σ : AccountMap) (μ : MachineState) (μₛ : Stack UInt256) (A : Substate) :=
      if μ.gasAvailable >= Cextra σ μₛ A then min (L (μ.gasAvailable - Cextra σ μₛ A)) μₛ[0]! else μₛ[0]!

    Ccallgas (σ : AccountMap) (μₛ : Stack UInt256) (A : Substate) :=
      if μₛ[2]! != 0 then Cgascap σ μ μₛ A + Gcallstipend else Cgascap σ μ μₛ A

/--
(65)
-/
def R (x : UInt256) : UInt256 := Ginitcodeword * (x / 32 : ℚ).ceil

/--
H.1. Gas Cost - the third summand.

NB Stack accesses are assumed guarded here and we access with `!`.
This is for keeping in sync with the way the YP is structures, at least for the time being.
-/
private def C' (s : State) (instr : Operation .EVM) : Except EVM.Exception UInt256 :=
  let { accountMap := σ, stack := μₛ, substate := A, toMachineState := μ, executionEnv := I, ..} := s
  match instr with
    | .SSTORE => Csstore s
    | .EXP => let μ₁ := μₛ[1]!; return if μ₁ == 0 then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 μ₁) -- TODO(check) I think this floors by itself. cf. H.1. YP.
    | .EXTCODECOPY => return Caccess (Address.ofUInt256 μₛ[0]!) A
    | .LOG0 => return Glog + Glogdata * μₛ[1]!
    | .LOG1 => return Glog + Glogdata * μₛ[1]! + Glogtopic
    | .LOG2 => return Glog + Glogdata * μₛ[1]! + 2 * Glogtopic
    | .LOG3 => return Glog + Glogdata * μₛ[1]! + 3 * Glogtopic
    | .LOG4 => return Glog + Glogdata * μₛ[1]! + 4 * Glogtopic
    | .SELFDESTRUCT => return Cselfdestruct s
    | .CREATE => return Gcreate + R μₛ[2]!
    | .CREATE2 => let μ₂ := μₛ[2]!; return Gcreate + Gkeccak256word * (μ₂ / 32 : ℚ).ceil + R μ₂
    | .KECCAK256 => return Gkeccak256 + Gkeccak256word * (μₛ[1]! / 32 : ℚ).ceil
    | .JUMPDEST => return Gjumpdest
    | .SLOAD => return Csload μₛ A I
    | .BLOCKHASH => return Gblockhash
    | w => pure <|
      if w ∈ Wcopy then Gverylow + Gcopy * (μₛ[2]! / 32 : ℚ).ceil else
      if w ∈ Wextaccount then Caccess (Address.ofUInt256 μₛ[0]!) A else
      if w ∈ Wcall then Ccall μₛ σ μ A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      -- TODO: MCOPY, TLOAD, TSTORE, DIFFICULTY
      dbg_trace s!"TODO - C called with an unknown instruction: {w.pretty}"; 42

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/
def C (s : EVM.State) (μ'ᵢ : UInt256) (instr : Operation .EVM) : Except EVM.Exception UInt256 := do
  let { toMachineState := μ, ..} := s
  pure <| Cₘ μ'ᵢ - Cₘ μ.activeWords + (← C' s instr)

end Gas

end EVM

end EvmYul
