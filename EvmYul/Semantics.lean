import EvmYul.Operations

import EvmYul.Yul.State
import EvmYul.Yul.Ast
import EvmYul.Yul.Exception
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.PrimOps
import EvmYul.EVM.StateOps
import EvmYul.Wheels

import EvmYul.UInt256
import EvmYul.StateOps
import EvmYul.SharedStateOps
import EvmYul.MachineStateOps

import EvmYul.SpongeHash.Keccak256

--

import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

--

namespace EvmYul

section Semantics

open Stack

/--
`Transformer` is the primop-evaluating semantic function type for `Yul` and `EVM`.

- `EVM` is `EVM.State → EVM.State` because the arguments are already contained in `EVM.State.stack`.
- `Yul` is `Yul.State × List Literal → Yul.State × Option Literal` because the evaluation of primops in Yul
  does *not* store results within the state.

Both operations happen in their respecitve `.Exception` error monad.
-/
private abbrev Transformer : OperationType → Type
  | .EVM => EVM.Transformer
  | .Yul => Yul.Transformer

private def dispatchInvalid (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => λ _ ↦ .error .InvalidInstruction
    | .Yul => λ _ _ ↦ .error Yul.Exception.InvalidInstruction

private def dispatchUnary (τ : OperationType) : Primop.Unary → Transformer τ :=
  match τ with
    | .EVM => EVM.execUnOp
    | .Yul => Yul.execUnOp

private def dispatchBinary (τ : OperationType) : Primop.Binary → Transformer τ :=
  match τ with
    | .EVM => EVM.execBinOp
    | .Yul => Yul.execBinOp

private def dispatchTernary (τ : OperationType) : Primop.Ternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execTriOp
    | .Yul => Yul.execTriOp

private def dispatchQuartiary (τ : OperationType) : Primop.Quaternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execQuadOp
    | .Yul => Yul.execQuadOp

private def dispatchExecutionEnvOp (τ : OperationType) (op : ExecutionEnv → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.executionEnvOp op
    | .Yul => Yul.executionEnvOp op

private def dispatchUnaryExecutionEnvOp (τ : OperationType) (op : ExecutionEnv → UInt256 → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryExecutionEnvOp op
    | .Yul => Yul.unaryExecutionEnvOp op

private def dispatchMachineStateOp (τ : OperationType) (op : MachineState → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.machineStateOp op
    | .Yul => Yul.machineStateOp op

private def dispatchUnaryStateOp (τ : OperationType) (op : State → UInt256 → State × UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryStateOp op
    | .Yul => Yul.unaryStateOp op

private def dispatchTernaryCopyOp
 (τ : OperationType) (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryCopyOp op
    | .Yul => Yul.ternaryCopyOp op

private def dispatchQuaternaryCopyOp
 (τ : OperationType) (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.quaternaryCopyOp op
    | .Yul => Yul.quaternaryCopyOp op

private def dispatchBinaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp op
    | .Yul => Yul.binaryMachineStateOp op

private def dispatchTernaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryMachineStateOp op
    | .Yul => Yul.ternaryMachineStateOp op

private def dispatchBinaryMachineStateOp'
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp' op
    | .Yul => Yul.binaryMachineStateOp' op

private def dispatchBinaryStateOp
 (τ : OperationType) (op : State → UInt256 → UInt256 → State) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryStateOp op
    | .Yul => Yul.binaryStateOp op

private def dispatchStateOp (τ : OperationType) (op : State → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.stateOp op
    | .Yul => Yul.stateOp op

private def dispatchLog0 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log0Op
    | .Yul => Yul.log0Op

private def dispatchLog1 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log1Op
    | .Yul => Yul.log1Op

private def dispatchLog2 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log2Op
    | .Yul => Yul.log2Op

private def dispatchLog3 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log3Op
    | .Yul => Yul.log3Op

private def dispatchLog4 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log4Op
    | .Yul => Yul.log4Op

private def L (n : ℕ) := n - n / 64

def dup (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

-- TODO: Yul halting for `SELFDESTRUCT`, `RETURN`, `REVERT`, `STOP`
def step {τ : OperationType} (op : Operation τ) (arg : Option (UInt256 × Nat) := .none) : Transformer τ := Id.run do
  let log : Id Unit :=
    match τ with
      | .EVM => dbg_trace op.pretty; pure ()
      | .Yul => pure ()
  match τ, op with
    -- TODO: Revisit STOP, this is likely not the best way to do it and the Yul version is WIP.
    | τ, .STOP =>
      match τ with
        | .EVM => λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
        | .Yul => λ yulState _ ↦ .ok (yulState, none)
    | τ, .ADD =>
      dispatchBinary τ UInt256.add
    | τ, .MUL =>
      dispatchBinary τ UInt256.mul
    | τ, .SUB =>
      dispatchBinary τ UInt256.sub
    | τ, .DIV =>
      dispatchBinary τ UInt256.div
    | τ, .SDIV =>
      dispatchBinary τ UInt256.sdiv
    | τ, .MOD =>
      dispatchBinary τ UInt256.mod
    | τ, .SMOD =>
      dispatchBinary τ UInt256.smod
    | τ, .ADDMOD =>
      dispatchTernary τ UInt256.addMod
    | τ, .MULMOD =>
      dispatchTernary τ UInt256.mulMod
    | τ, .EXP =>
      dispatchBinary τ UInt256.exp
    | τ, .SIGNEXTEND =>
      dispatchBinary τ UInt256.signextend
    | τ, .LT =>
      dispatchBinary τ UInt256.lt
    | τ, .GT =>
      dispatchBinary τ UInt256.gt
    | τ, .SLT =>
      dispatchBinary τ UInt256.slt
    | τ, .SGT =>
      dispatchBinary τ UInt256.sgt
    | τ, .EQ =>
      dispatchBinary τ UInt256.eq
    | τ, .ISZERO =>
      dispatchUnary τ UInt256.isZero
    | τ, .AND =>
      dispatchBinary τ UInt256.land
    | τ, .OR =>
      dispatchBinary τ UInt256.lor
    | τ, .XOR =>
      dispatchBinary τ UInt256.xor
    | τ, .NOT =>
      dispatchUnary τ UInt256.lnot
    | τ, .BYTE =>
      dispatchBinary τ UInt256.byteAt
    | τ, .SHL =>
      dispatchBinary τ (flip UInt256.shiftLeft)
    | τ, .SHR =>
      dispatchBinary τ (flip UInt256.shiftRight)
    | τ, .SAR =>
      dispatchBinary τ UInt256.sar

    | τ, .KECCAK256 =>
      dispatchBinaryMachineStateOp' τ MachineState.keccak256

    | τ, .ADDRESS =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | τ, .BALANCE =>
      dispatchUnaryStateOp τ EvmYul.State.balance
    | τ, .ORIGIN =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | τ, .CALLER =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | τ, .CALLVALUE =>
      dispatchExecutionEnvOp τ ExecutionEnv.weiValue
    | τ, .CALLDATALOAD =>
      dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | τ, .CALLDATASIZE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.inputData)
    | τ, .CALLDATACOPY =>
      dispatchTernaryCopyOp τ .calldatacopy
    | τ, .CODESIZE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | τ, .CODECOPY =>
      dispatchTernaryCopyOp τ .codeCopy
    | τ, .GASPRICE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ExecutionEnv.gasPrice)
    | τ, .EXTCODESIZE =>
      dispatchUnaryStateOp τ EvmYul.State.extCodeSize
    | τ, .EXTCODECOPY =>
      dispatchQuaternaryCopyOp τ EvmYul.SharedState.extCodeCopy'
    | τ, .RETURNDATASIZE =>
      dispatchMachineStateOp τ EvmYul.MachineState.returndatasize
    | .EVM, .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .Yul, .RETURNDATACOPY =>
      λ yulState lits ↦
        match lits with
          | [a, b, c] => do
            let mState' := yulState.toSharedState.toMachineState.returndatacopy a b c
            .ok <| (yulState.setMachineState mState', .none)
          | _ => .error .InvalidArguments
    | τ, .EXTCODEHASH => dispatchUnaryStateOp τ EvmYul.State.extCodeHash

    | τ, .BLOCKHASH => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | τ, .COINBASE => dispatchStateOp τ (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | τ, .TIMESTAMP =>
      dispatchStateOp τ EvmYul.State.timeStamp
    | τ, .NUMBER => dispatchStateOp τ EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | τ, .PREVRANDAO => dispatchExecutionEnvOp τ EvmYul.prevRandao
    | τ, .GASLIMIT => dispatchStateOp τ EvmYul.State.gasLimit
    | τ, .CHAINID => dispatchStateOp τ EvmYul.State.chainId
    | τ, .SELFBALANCE => dispatchStateOp τ EvmYul.State.selfbalance
    | τ, .BASEFEE => dispatchExecutionEnvOp τ EvmYul.basefee
    | τ, .BLOBHASH => dispatchUnaryExecutionEnvOp τ blobhash
    | τ, .BLOBBASEFEE => dispatchExecutionEnvOp τ EvmYul.ExecutionEnv.getBlobGasprice

    | .EVM, .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .EVM, .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow
    | .Yul, .MLOAD => λ yulState lits ↦
        match lits with
          | [a] =>
            let (v, mState') := yulState.toSharedState.toMachineState.mload a
            let yulState' := yulState.setMachineState mState'
            .ok <| (yulState', some v)
          | _ => .error .InvalidArguments
    | τ, .MSTORE =>
      dispatchBinaryMachineStateOp τ MachineState.mstore
    | τ, .MSTORE8 => dispatchBinaryMachineStateOp τ MachineState.mstore8
    | τ, .SLOAD =>
      dispatchUnaryStateOp τ EvmYul.State.sload
    | τ, .SSTORE =>
      dispatchBinaryStateOp τ EvmYul.State.sstore
    | τ, .TLOAD => dispatchUnaryStateOp τ EvmYul.State.tload
    | τ, .TSTORE => dispatchBinaryStateOp τ EvmYul.State.tstore
    | τ, .MSIZE => dispatchMachineStateOp τ MachineState.msize
    | τ, .GAS =>
      dispatchMachineStateOp τ MachineState.gas
    | τ, .MCOPY => dispatchTernaryMachineStateOp τ MachineState.mcopy

    | τ, .LOG0 => dispatchLog0 τ
    | τ, .LOG1 => dispatchLog1 τ
    | τ, .LOG2 => dispatchLog2 τ
    | τ, .LOG3 => dispatchLog3 τ
    | τ, .LOG4 => dispatchLog4 τ

    | .Yul, .CREATE => λ yulState lits ↦
        match lits with
          | [v, poz, len] =>
            let Iₐ := yulState.executionEnv.codeOwner
            let nonce' : UInt256 := yulState.toState.accountMap.find? Iₐ |>.option ⟨0⟩ (·.nonce)
            let s : 𝕋 := .𝔹 (toBytesBigEndian Iₐ.val).toByteArray
            let n : 𝕋 := .𝔹 (toBytesBigEndian nonce'.toNat).toByteArray
            let L_A := RLP <| .𝕃 [s, n]
            match L_A with
              | none => .error .NotEncodableRLP
              | some L_A =>
                let addr : AccountAddress :=
                  (ffi.KEC L_A).extract 12 32 /- 160 bits = 20 bytes -/
                    |> fromByteArrayBigEndian |> Fin.ofNat
                let code := yulState.toMachineState.memory.readWithPadding poz.toNat len.toNat
                match yulState.toState.accountMap.find? Iₐ with
                  | none => .ok <| (yulState, some ⟨0⟩)
                  | some ac_Iₐ =>
                    if v < ac_Iₐ.balance then .ok <| (yulState, some ⟨0⟩) else
                    let ac_Iₐ := {ac_Iₐ with balance := ac_Iₐ.balance - v, nonce := ac_Iₐ.nonce + ⟨1⟩}
                    let v' :=
                      match yulState.toState.accountMap.find? addr with
                        | none => ⟨0⟩
                        | some ac_addr => ac_addr.balance
                    let newAccount : Account :=
                      { nonce := ⟨1⟩
                      , balance := v + v'
                      , code := code
                      , storage := default
                      , tstorage := default
                      }
                    let yulState' :=
                      yulState.setState <|
                        yulState.toState.updateAccount addr newAccount
                        |>.updateAccount Iₐ ac_Iₐ

                    .ok <| (yulState', some (.ofNat addr))
          | _ => .error .InvalidArguments
    | τ, .RETURN => dispatchBinaryMachineStateOp τ MachineState.evmReturn
    | τ, .REVERT => dispatchBinaryMachineStateOp τ MachineState.evmRevert
    | .EVM, .SELFDESTRUCT =>
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let Iₐ := evmState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 μ₁
            if evmState.createdAccounts.contains Iₐ then
              -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
              let A' : Substate :=
                { evmState.substate with
                    selfDestructSet :=
                      evmState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          evmState.accountMap.insert r {σ_r with balance := ⟨0⟩}
                            |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
            else
              /- When SELFDESTRUCT is executed in a transaction that is not the
                same as the contract calling SELFDESTRUCT was created:
              -/
              let A' : Substate :=
                { evmState.substate with
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- Note that if the target is the same as the contract
                          -- calling SELFDESTRUCT there is no net change in balances.
                          -- Unlike the prior specification, Ether will not be burnt in this case.
                          evmState.accountMap
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow
    | .Yul, .SELFDESTRUCT => λ yulState lits ↦
      match lits with
        | [a] =>
            let Iₐ := yulState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 a
              let A' : Substate :=
                { yulState.toState.substate with
                    selfDestructSet :=
                      yulState.toState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      yulState.toState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match yulState.toState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; yulState.toState.accountMap
                  | some σ_Iₐ  =>
                    match yulState.toState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          yulState.toState.accountMap
                        else
                          yulState.toState.accountMap.insert r
                            {(default : Account) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          yulState.toState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          yulState.toState.accountMap.insert r {σ_r with balance := ⟨0⟩}
                            |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
              let yulState' :=
                yulState.setState
                  { yulState.toState with accountMap := accountMap', substate := A'}
              .ok <| (yulState', none)
        | _ => .error .InvalidArguments
    | τ, .INVALID => dispatchInvalid τ

    | .Yul, .CREATE2 => λ yulState lits ↦
        match lits with
          | [v, poz, len, ζ] =>
            let Iₐ := yulState.executionEnv.codeOwner
            let this₀ := toBytesBigEndian Iₐ.val
            let this : List UInt8 := List.replicate (20 - this₀.length) 0 ++ this₀
            let code := yulState.toMachineState.memory.readWithPadding poz.toNat len.toNat
            let s : List UInt8 := toBytesBigEndian ζ.toNat
            let a₀ : List UInt8 := [0xff]
            let addr₀ := ffi.KEC <| ⟨⟨a₀ ++ this ++ s⟩⟩ ++ ffi.KEC code
            let addr : AccountAddress := Fin.ofNat <| fromByteArrayBigEndian addr₀
            match yulState.toState.accountMap.find? Iₐ with
              | none => .ok <| (yulState, some ⟨0⟩)
              | some ac_Iₐ =>
                if v < ac_Iₐ.balance then .ok <| (yulState, some ⟨0⟩) else
                let ac_Iₐ' := {ac_Iₐ with balance := ac_Iₐ.balance - v, nonce := ac_Iₐ.nonce + ⟨1⟩}
                let v' :=
                  match yulState.toState.accountMap.find? addr with
                    | none => ⟨0⟩
                    | some ac_addr => ac_addr.balance
                let newAccount : Account :=
                  { nonce := ⟨1⟩
                  , balance := v + v'
                  , code := code
                  , storage := default
                  , tstorage := default
                  }
                let yulState' :=
                  yulState.setState <|
                    yulState.toState.updateAccount addr newAccount
                      |>.updateAccount Iₐ ac_Iₐ'

                .ok <| (yulState', some (.ofNat addr))
          | _ => .error .InvalidArguments
    | .EVM, .Push .PUSH0 => λ evmState =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push ⟨0⟩)
    | .EVM, .Push _ => λ evmState => do
        let some (arg, argWidth) := arg | .error .StackUnderflow
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
    | .EVM, .JUMP => λ evmState => do
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .JUMPI => λ evmState => do
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmState.pc + ⟨1⟩
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .PC => λ evmState =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
    | .EVM, .JUMPDEST => λ evmState => do
        .ok <| evmState.incrPC
    | .EVM, .DUP1 => dup 1
    | .EVM, .DUP2 => dup 2
    | .EVM, .DUP3 => dup 3
    | .EVM, .DUP4 => dup 4
    | .EVM, .DUP5 => dup 5
    | .EVM, .DUP6 => dup 6
    | .EVM, .DUP7 => dup 7
    | .EVM, .DUP8 => dup 8
    | .EVM, .DUP9 => dup 9
    | .EVM, .DUP10 => dup 10
    | .EVM, .DUP11 => dup 11
    | .EVM, .DUP12 => dup 12
    | .EVM, .DUP13 => dup 13
    | .EVM, .DUP14 => dup 14
    | .EVM, .DUP15 => dup 15
    | .EVM, .DUP16 => dup 16
    | .EVM, .SWAP1 => swap 1
    | .EVM, .SWAP2 => swap 2
    | .EVM, .SWAP3 => swap 3
    | .EVM, .SWAP4 => swap 4
    | .EVM, .SWAP5 => swap 5
    | .EVM, .SWAP6 => swap 6
    | .EVM, .SWAP7 => swap 7
    | .EVM, .SWAP8 => swap 8
    | .EVM, .SWAP9 => swap 9
    | .EVM, .SWAP10 => swap 10
    | .EVM, .SWAP11 => swap 11
    | .EVM, .SWAP12 => swap 12
    | .EVM, .SWAP13 => swap 13
    | .EVM, .SWAP14 => swap 14
    | .EVM, .SWAP15 => swap 15
    | .EVM, .SWAP16 => swap 16
    | .EVM, _ => λ _ ↦ default
    | .Yul, _ => λ _ _ ↦ default


end Semantics

end EvmYul
