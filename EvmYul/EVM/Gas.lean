import EvmYul.Maps.YPState
import EvmYul.MachineState
import EvmYul.State.Substate
import EvmYul.State.ExecutionEnv
import EvmYul.EVM.Exception

namespace EvmYul

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
def Cₘ(a : UInt256) : ℕ := Gmemory * a + ((a * a) / QuadraticCeofficient) -- TODO(check) - What is subject to `% 2^256` here?
                                                                          --               Note that the YP takes an explicit floor, we have division in Nat.
  where QuadraticCeofficient : ℕ := 512

/--
H.1. Gas Cost - the remaining summand.
-/
private def C' (σ : YPState) (μ : MachineState) (μ'ᵢ : UInt256)
               (instr : Operation .EVM) (A : Substate) (I : ExecutionEnv) : UInt256 := sorry
  where STOP : Operation .EVM × Option (UInt256 × ℕ) := (Operation.STOP, Option.none)
        -- /--
        -- (327)

        -- NB this should be `Option.get!`-able but I'd rather not hard crash for the time being and log the error.
        -- -/

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/
def C (σ : YPState) (μ : MachineState) (μ'ᵢ : UInt256)
      (instr : Operation .EVM) (A : Substate) (I : ExecutionEnv) : UInt256 :=
  Cₘ μ'ᵢ - Cₘ μ.activeWords + C' σ μ μ'ᵢ instr A I
  -- where STOP : Operation .EVM × Option (UInt256 × ℕ) := (Operation.STOP, Option.none)
  --       /--
  --       (327)

  --       NB this should be `Option.get!`-able but I'd rather not hard crash for the time being and log the error.
  --       -/
  --       -- w := if pc < I.code.size
  --       --      then match EVM.decode I.code pc with
  --       --             | .none => dbg_trace s!"TODO - This should always succeed."; STOP
  --       --             | .some instr => instr
  --       --      else STOP
  --       -- μ'i :=

end Gas

end EvmYul
