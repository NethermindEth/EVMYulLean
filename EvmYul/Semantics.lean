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

namespace EvmYul

section Semantics

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

private def dispatchUnary (debugMode : Bool) (τ : OperationType) : Primop.Unary → Transformer τ :=
  match τ with
    | .EVM => EVM.execUnOp debugMode
    | .Yul => Yul.execUnOp

private def dispatchBinary (debugMode : Bool) (τ : OperationType) : Primop.Binary → Transformer τ :=
  match τ with
    | .EVM => EVM.execBinOp debugMode
    | .Yul => Yul.execBinOp

private def dispatchTernary (debugMode : Bool) (τ : OperationType) : Primop.Ternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execTriOp debugMode
    | .Yul => Yul.execTriOp

private def dispatchQuartiary (debugMode : Bool) (τ : OperationType) : Primop.Quaternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execQuadOp debugMode
    | .Yul => Yul.execQuadOp

private def dispatchExecutionEnvOp (debugMode : Bool) (τ : OperationType) (op : ExecutionEnv → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.executionEnvOp debugMode op
    | .Yul => Yul.executionEnvOp op

private def dispatchUnaryExecutionEnvOp (debugMode : Bool) (τ : OperationType) (op : ExecutionEnv → UInt256 → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryExecutionEnvOp debugMode op
    | .Yul => Yul.unaryExecutionEnvOp op

private def dispatchMachineStateOp (debugMode : Bool) (τ : OperationType) (op : MachineState → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.machineStateOp debugMode op
    | .Yul => Yul.machineStateOp op

private def dispatchUnaryStateOp (debugMode : Bool) (τ : OperationType) (op : State → UInt256 → State × UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryStateOp debugMode op
    | .Yul => Yul.unaryStateOp op

private def dispatchTernaryCopyOp
  (debugMode : Bool) (τ : OperationType) (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryCopyOp debugMode op
    | .Yul => Yul.ternaryCopyOp op

private def dispatchQuaternaryCopyOp
  (debugMode : Bool) (τ : OperationType) (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.quaternaryCopyOp (debugMode : Bool) op
    | .Yul => Yul.quaternaryCopyOp op

private def dispatchBinaryMachineStateOp
  (debugMode : Bool) (τ : OperationType) (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp debugMode op
    | .Yul => Yul.binaryMachineStateOp op

private def dispatchTernaryMachineStateOp
  (debugMode : Bool) (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryMachineStateOp debugMode op
    | .Yul => Yul.ternaryMachineStateOp op

private def dispatchBinaryMachineStateOp'
  (debugMode : Bool) (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp' debugMode op
    | .Yul => Yul.binaryMachineStateOp' op

private def dispatchBinaryStateOp
  (debugMode : Bool) (τ : OperationType) (op : State → UInt256 → UInt256 → State) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryStateOp debugMode op
    | .Yul => Yul.binaryStateOp op

private def dispatchStateOp (debugMode : Bool) (τ : OperationType) (op : State → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.stateOp debugMode op
    | .Yul => Yul.stateOp op

private def dispatchLog0 (debugMode : Bool) (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log0Op debugMode
    | .Yul => Yul.log0Op

private def dispatchLog1 (debugMode : Bool) (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log1Op debugMode
    | .Yul => Yul.log1Op

private def dispatchLog2 (debugMode : Bool) (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log2Op debugMode
    | .Yul => Yul.log2Op

private def dispatchLog3 (debugMode : Bool) (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log3Op debugMode
    | .Yul => Yul.log3Op

private def dispatchLog4 (debugMode : Bool) (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log4Op debugMode
    | .Yul => Yul.log4Op

private def L (n : ℕ) := n - n / 64

def shortInput := "01aHHABLA"
def longInput := "Lean 4 is a reimplementation of the Lean theorem prover in Lean itself. The new compiler produces C code, and users can now implement efficient proof automation in Lean, compile it into efficient C code, and load it as a plugin. In Lean 4, users can access all internal data structures used to implement Lean by merely importing the Lean package."

-- example :
--   toHex (KEC shortInput.toUTF8) = "6107589dda3ff2ac99745795d1eb3ac2538f2a7a93f9ef180c33dee244592874"
-- := by native_decide

-- example :
--   toHex (KEC longInput.toUTF8) = "596cfd6c2f8f76b8f480f5c2fc582db9089486792435f397f8286aff64d42646"
-- := by native_decide

-- TODO: Yul halting for `SELFDESTRUCT`, `RETURN`, `REVERT`, `STOP`
def step {τ : OperationType} (debugMode : Bool) (op : Operation τ) : Transformer τ := Id.run do
  let log : Id Unit :=
    match τ with
      | .EVM => dbg_trace op.pretty; pure ()
      | .Yul => pure ()
  if debugMode then log
  match τ, op with
    -- TODO: Revisit STOP, this is likely not the best way to do it and the Yul version is WIP.
    | τ, .STOP =>
      match τ with
        | .EVM => λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
        | .Yul => λ yulState _ ↦ .ok (yulState, none)
    | τ, .ADD =>
      dispatchBinary debugMode τ UInt256.add
    | τ, .MUL =>
      dispatchBinary debugMode τ UInt256.mul
    | τ, .SUB =>
      dispatchBinary debugMode τ UInt256.sub
    | τ, .DIV =>
      dispatchBinary debugMode τ UInt256.div
    | τ, .SDIV =>
      dispatchBinary debugMode τ UInt256.sdiv
    | τ, .MOD =>
      dispatchBinary debugMode τ UInt256.mod
    | τ, .SMOD =>
      dispatchBinary debugMode τ UInt256.smod
    | τ, .ADDMOD =>
      dispatchTernary debugMode τ UInt256.addMod
    | τ, .MULMOD =>
      dispatchTernary debugMode τ UInt256.mulMod
    | τ, .EXP =>
      dispatchBinary debugMode τ UInt256.exp
    | τ, .SIGNEXTEND =>
      dispatchBinary debugMode τ UInt256.signextend
    | τ, .LT =>
      dispatchBinary debugMode τ UInt256.lt
    | τ, .GT =>
      dispatchBinary debugMode τ UInt256.gt
    | τ, .SLT =>
      dispatchBinary debugMode τ UInt256.slt
    | τ, .SGT =>
      dispatchBinary debugMode τ UInt256.sgt
    | τ, .EQ =>
      dispatchBinary debugMode τ UInt256.eq
    | τ, .ISZERO =>
      dispatchUnary debugMode τ UInt256.isZero
    | τ, .AND =>
      dispatchBinary debugMode τ UInt256.land
    | τ, .OR =>
      dispatchBinary debugMode τ UInt256.lor
    | τ, .XOR =>
      dispatchBinary debugMode τ UInt256.xor
    | τ, .NOT =>
      dispatchUnary debugMode τ UInt256.lnot
    | τ, .BYTE =>
      dispatchBinary debugMode τ UInt256.byteAt
    | τ, .SHL =>
      dispatchBinary debugMode τ (flip UInt256.shiftLeft)
    | τ, .SHR =>
      dispatchBinary debugMode τ (flip UInt256.shiftRight)
    | τ, .SAR =>
      dispatchBinary debugMode τ UInt256.sar

    | τ, .KECCAK256 =>
      dispatchBinaryMachineStateOp' debugMode τ MachineState.keccak256

    | τ, .ADDRESS =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | τ, .BALANCE =>
      dispatchUnaryStateOp debugMode τ EvmYul.State.balance
    | τ, .ORIGIN =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | τ, .CALLER =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | τ, .CALLVALUE =>
      dispatchExecutionEnvOp debugMode τ ExecutionEnv.weiValue
    | τ, .CALLDATALOAD =>
      dispatchUnaryStateOp debugMode τ (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | τ, .CALLDATASIZE =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.inputData)
    | τ, .CALLDATACOPY =>
      dispatchTernaryCopyOp debugMode τ .calldatacopy
    | τ, .CODESIZE =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | τ, .CODECOPY =>
      dispatchTernaryCopyOp debugMode τ .codeCopy
    | τ, .GASPRICE =>
      dispatchExecutionEnvOp debugMode τ (.ofNat ∘ ExecutionEnv.gasPrice)
    | τ, .EXTCODESIZE =>
      dispatchUnaryStateOp debugMode τ EvmYul.State.extCodeSize
    | τ, .EXTCODECOPY =>
      dispatchQuaternaryCopyOp debugMode τ EvmYul.SharedState.extCodeCopy'
    | τ, .RETURNDATASIZE =>
      dispatchMachineStateOp debugMode τ EvmYul.MachineState.returndatasize
    | .EVM, .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            if debugMode then
              dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}"
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
    | τ, .EXTCODEHASH => dispatchUnaryStateOp debugMode τ EvmYul.State.extCodeHash

    | τ, .BLOCKHASH => dispatchUnaryStateOp debugMode τ (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | τ, .COINBASE => dispatchStateOp debugMode τ (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | τ, .TIMESTAMP =>
      dispatchStateOp debugMode τ EvmYul.State.timeStamp
    | τ, .NUMBER => dispatchStateOp debugMode τ EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | τ, .PREVRANDAO => dispatchExecutionEnvOp debugMode τ EvmYul.prevRandao
    | τ, .GASLIMIT => dispatchStateOp debugMode τ EvmYul.State.gasLimit
    | τ, .CHAINID => dispatchStateOp debugMode τ EvmYul.State.chainId
    | τ, .SELFBALANCE => dispatchStateOp debugMode τ EvmYul.State.selfbalance
    | τ, .BASEFEE => dispatchExecutionEnvOp debugMode τ EvmYul.basefee
    | τ, .BLOBHASH => dispatchUnaryExecutionEnvOp debugMode τ blobhash
    | τ, .BLOBBASEFEE => dispatchExecutionEnvOp debugMode τ EvmYul.ExecutionEnv.getBlobGasprice

    | .EVM, .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .EVM, .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          if debugMode then
            dbg_trace s!"called with μ₀: {μ₀}"
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
      dispatchBinaryMachineStateOp debugMode τ MachineState.mstore
    | τ, .MSTORE8 => dispatchBinaryMachineStateOp debugMode τ MachineState.mstore8
    | τ, .SLOAD =>
      dispatchUnaryStateOp debugMode τ EvmYul.State.sload
    | τ, .SSTORE =>
      dispatchBinaryStateOp debugMode τ EvmYul.State.sstore
    | τ, .TLOAD => dispatchUnaryStateOp debugMode τ EvmYul.State.tload
    | τ, .TSTORE => dispatchBinaryStateOp debugMode τ EvmYul.State.tstore
    | τ, .MSIZE => dispatchMachineStateOp debugMode τ MachineState.msize
    | τ, .GAS =>
      dispatchMachineStateOp debugMode τ MachineState.gas
    | τ, .MCOPY => dispatchTernaryMachineStateOp debugMode τ MachineState.mcopy

    | τ, .LOG0 => dispatchLog0 debugMode τ
    | τ, .LOG1 => dispatchLog1 debugMode τ
    | τ, .LOG2 => dispatchLog2 debugMode τ
    | τ, .LOG3 => dispatchLog3 debugMode τ
    | τ, .LOG4 => dispatchLog4 debugMode τ

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
                  (KEC L_A).extract 12 32 /- 160 bits = 20 bytes -/
                    |>.data.data |> fromBytesBigEndian |> Fin.ofNat
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
    | τ, .RETURN => dispatchBinaryMachineStateOp debugMode τ MachineState.evmReturn
    | τ, .REVERT => dispatchBinaryMachineStateOp debugMode τ MachineState.evmRevert
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
            let addr₀ := KEC <| ⟨⟨a₀ ++ this ++ s⟩⟩ ++ KEC code
            let addr : AccountAddress := Fin.ofNat <| fromBytesBigEndian addr₀.data.data
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

    | .Yul, _ => λ _ _ ↦ default
    | .EVM, _ => λ _ ↦ default

end Semantics

end EvmYul
