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
    | .EVM => λ _ ↦ .error EVM.Exception.InvalidInstruction
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

def shortInput := "01aHHABLA"
def longInput := "Lean 4 is a reimplementation of the Lean theorem prover in Lean itself. The new compiler produces C code, and users can now implement efficient proof automation in Lean, compile it into efficient C code, and load it as a plugin. In Lean 4, users can access all internal data structures used to implement Lean by merely importing the Lean package."

example :
  toHex (KEC shortInput.toUTF8) = "6107589dda3ff2ac99745795d1eb3ac2538f2a7a93f9ef180c33dee244592874"
:= by native_decide

example :
  toHex (KEC longInput.toUTF8) = "596cfd6c2f8f76b8f480f5c2fc582db9089486792435f397f8286aff64d42646"
:= by native_decide

inductive 𝕋 :=
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋

def BE : ℕ → ByteArray := List.toByteArray ∘ toBytesBigEndian

private def R_b (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x.get! 0 < 128 then some x
  else
    if x.size < 56 then some <| [⟨128 + x.size⟩].toByteArray ++ x
    else
      if x.size < 2^64 then
        let be := BE x.size
        some <| [⟨183 + be.size⟩].toByteArray ++ be ++ x
      else none

mutual

private def s (l : List 𝕋) : Option ByteArray :=
  match l with
    | [] => some .empty
    | t :: ts =>
      match RLP t, s ts with
        | none     , _         => none
        | _        , none      => none
        | some rlpₗ, some rlpᵣ => rlpₗ ++ rlpᵣ

def R_l (l : List 𝕋) : Option ByteArray :=
  match s l with
    | none => none
    | some s_x =>
      if s_x.size < 56 then
        some <| [⟨192 + s_x.size⟩].toByteArray ++ s_x
      else
        if s_x.size < 2^64 then
          let be := BE s_x.size
          some <| [⟨247 + be.size⟩].toByteArray ++ be ++ s_x
        else none

def RLP (t : 𝕋) : Option ByteArray :=
  match t with
    | .𝔹 ba => R_b ba
    | .𝕃 l => R_l l
end

def step {τ : OperationType} (op : Operation τ) : Transformer τ :=
  match τ, op with
    -- TODO: Revisit STOP, this is likely not the best way to do it and the Yul version is WIP.
    | τ, .STOP =>
      match τ with
        | .EVM => λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
        | .Yul => λ yulState _ ↦ .ok (yulState, none)
    | τ, .ADD => dispatchBinary τ UInt256.add
    | τ, .MUL => dispatchBinary τ UInt256.mul
    | τ, .SUB => dispatchBinary τ UInt256.add
    | τ, .DIV => dispatchBinary τ UInt256.div
    | τ, .SDIV => dispatchBinary τ UInt256.sdiv
    | τ, .MOD => dispatchBinary τ UInt256.mod
    | τ, .SMOD => dispatchBinary τ UInt256.smod
    | τ, .ADDMOD => dispatchTernary τ UInt256.addMod
    | τ, .MULMOD => dispatchTernary τ UInt256.mulMod
    | τ, .EXP => dispatchBinary τ UInt256.exp
    | τ, .SIGNEXTEND => dispatchBinary τ UInt256.signextend

    | τ, .LT => dispatchBinary τ UInt256.lt
    | τ, .GT => dispatchBinary τ UInt256.gt
    | τ, .SLT => dispatchBinary τ UInt256.slt
    | τ, .SGT => dispatchBinary τ UInt256.sgt
    | τ, .EQ => dispatchBinary τ UInt256.eq
    | τ, .ISZERO => dispatchUnary τ UInt256.isZero
    | τ, .AND => dispatchBinary τ UInt256.land
    | τ, .OR => dispatchBinary τ UInt256.lor
    | τ, .XOR => dispatchBinary τ UInt256.xor
    | τ, .NOT => dispatchUnary τ UInt256.lnot
    | τ, .BYTE => dispatchBinary τ UInt256.byteAt
    | τ, .SHL => dispatchBinary τ UInt256.shiftLeft
    | τ, .SHR => dispatchBinary τ UInt256.shiftRight
    | τ, .SAR => dispatchBinary τ UInt256.sar

    | τ, .KECCAK256 => dispatchBinaryMachineStateOp' τ MachineState.keccak256

    | τ, .ADDRESS => dispatchExecutionEnvOp τ (Fin.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | τ, .BALANCE => dispatchUnaryStateOp τ EvmYul.State.balance
    | τ, .ORIGIN => dispatchExecutionEnvOp τ (Fin.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | τ, .CALLER => dispatchExecutionEnvOp τ (Fin.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | τ, .CALLVALUE => dispatchExecutionEnvOp τ (Fin.ofNat ∘ Fin.val ∘ ExecutionEnv.weiValue)
    | τ, .CALLDATALOAD => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | τ, .CALLDATASIZE => dispatchExecutionEnvOp τ (.size ∘ ExecutionEnv.inputData)
    | τ, .CALLDATACOPY => dispatchTernaryCopyOp τ .calldatacopy
    | τ, .CODESIZE => dispatchExecutionEnvOp τ (.size ∘ ExecutionEnv.code)
    | τ, .CODECOPY => dispatchTernaryCopyOp τ .codeCopy
    | τ, .GASPRICE => dispatchExecutionEnvOp τ (.ofNat ∘ ExecutionEnv.gasPrice)
    | τ, .EXTCODESIZE => dispatchUnaryStateOp τ EvmYul.State.extCodeSize
    | τ, .EXTCODECOPY => dispatchQuaternaryCopyOp τ EvmYul.SharedState.extCodeCopy
    | τ, .RETURNDATASIZE => dispatchMachineStateOp τ EvmYul.MachineState.returndatasize
    | .EVM, .RETURNDATACOPY =>
      λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let .some mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
              | .error EVM.Exception.OutOfBounds
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error EVM.Exception.InvalidStackSizeException
    | .Yul, .RETURNDATACOPY =>
      λ yulState lits ↦
        match lits with
          | [a, b, c] => do
            let .some mState' := yulState.toSharedState.toMachineState.returndatacopy a b c
              | .error .InvalidArguments
            .ok <| (yulState.setMachineState mState', .none)
          | _ => .error .InvalidArguments
    | τ, .EXTCODEHASH => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.extCodeHash s v))

    | τ, .BLOCKHASH => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | τ, .COINBASE => dispatchStateOp τ (Fin.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | τ, .TIMESTAMP => dispatchStateOp τ EvmYul.State.timeStamp
    | τ, .NUMBER => dispatchStateOp τ EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | τ, .PREVRANDAO => sorry
    | τ, .DIFFICULTY => dispatchStateOp τ EvmYul.State.difficulty
    | τ, .GASLIMIT => dispatchStateOp τ EvmYul.State.gasLimit
    | τ, .CHAINID => dispatchStateOp τ EvmYul.State.chainId
    | τ, .SELFBALANCE => dispatchStateOp τ EvmYul.State.selfbalance

    | .EVM, .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error EVM.Exception.InvalidStackSizeException

    | .EVM, .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ =>
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error EVM.Exception.InvalidStackSizeException
    | .Yul, .MLOAD => λ yulState lits ↦
        match lits with
          | [a] =>
            let (v, mState') := yulState.toSharedState.toMachineState.mload a
            let yulState' := yulState.setMachineState mState'
            .ok <| (yulState', some v)
          | _ => .error .InvalidArguments
    | τ, .MSTORE => dispatchBinaryMachineStateOp τ MachineState.mstore
    | τ, .MSTORE8 => dispatchBinaryMachineStateOp τ MachineState.mstore8
    | τ, .SLOAD => dispatchUnaryStateOp τ EvmYul.State.sload
    | τ, .SSTORE => dispatchBinaryStateOp τ EvmYul.State.sstore
    | τ, .TLOAD => dispatchUnaryStateOp τ EvmYul.State.tload
    | τ, .TSTORE => dispatchBinaryStateOp τ EvmYul.State.tstore
    | τ, .MSIZE => dispatchMachineStateOp τ MachineState.msize
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
            let nonce' : UInt256 := yulState.toState.accountMap.lookup Iₐ |>.option 0 Account.nonce
            let s : 𝕋 := .𝔹 (toBytesBigEndian Iₐ.val).toByteArray
            let n : 𝕋 := .𝔹 (toBytesBigEndian nonce').toByteArray
            let L_A := RLP <| .𝕃 [s, n]
            match L_A with
              | none => .error .NotEncodableRLP
              | some L_A =>
                let addr : Address :=
                  (KEC L_A).extract 12 32 /- 160 bits = 20 bytes -/
                    |>.data.data |> fromBytesBigEndian |> Fin.ofNat
                let code : ByteArray := yulState.toMachineState.lookupMemoryRange poz len
                match yulState.toState.accountMap.lookup Iₐ with
                  | none => .ok <| (yulState, some 0)
                  | some ac_Iₐ =>
                    if v < ac_Iₐ.balance then .ok <| (yulState, some 0) else
                    let ac_Iₐ := {ac_Iₐ with balance := ac_Iₐ.balance - v, nonce := ac_Iₐ.nonce + 1}
                    let v' :=
                      match yulState.toState.accountMap.lookup addr with
                        | none => 0
                        | some ac_addr => ac_addr.balance
                    let newAccount : Account :=
                      { nonce := 1
                      , balance := v + v'
                      , code := code
                      , codeHash := fromBytesBigEndian (KEC code).data.data
                      , storage := default
                      , tstorage := default
                      }
                    let yulState' :=
                      yulState.setState <|
                        yulState.toState.updateAccount addr newAccount
                        |>.updateAccount Iₐ ac_Iₐ

                    .ok <| (yulState', some addr)
          | _ => .error .InvalidArguments
    | τ, .RETURN => dispatchBinaryMachineStateOp τ MachineState.evmReturn
    | τ, .REVERT => dispatchBinaryMachineStateOp τ MachineState.evmRevert
    | .EVM, .SELFDESTRUCT =>
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let Iₐ := evmState.executionEnv.codeOwner
            let r : Address := Address.ofUInt256 μ₁
            let A' : Substate :=
              { evmState.substate with
                  selfDestructSet := evmState.substate.selfDestructSet ∪ {Iₐ}
                  accessedAccounts := evmState.substate.accessedAccounts ∪ {r}
              }
            let accountMap' :=
              match evmState.lookupAccount r, evmState.lookupAccount Iₐ with
                | some σ_r, some σ_Iₐ =>
                  if r ≠ Iₐ then
                    evmState.accountMap.insert r
                      {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                        |>.insert Iₐ {σ_Iₐ with balance := 0}
                  else
                    evmState.accountMap.insert r {σ_r with balance := 0}
                      |>.insert Iₐ {σ_Iₐ with balance := 0}
                | _, _ => evmState.accountMap
            let evmState' :=
              {evmState with
                accountMap := accountMap'
                substate := A'
              }
            .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error EVM.Exception.InvalidStackSizeException
    | .EVM, .CALL => λ evmState ↦
      match evmState.stack.pop7 with
        | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ =>
          .ok <| sorry
        | _ => .error EVM.Exception.InvalidStackSizeException
    | τ, .INVALID => dispatchInvalid τ

    | .Yul, .CREATE2 => λ yulState lits ↦
        match lits with
          | [v, poz, len, ζ] =>
            let Iₐ := yulState.executionEnv.codeOwner
            let this₀ := toBytesBigEndian Iₐ.val
            let this : List UInt8 := List.replicate (20 - this₀.length) 0 ++ this₀
            let code : ByteArray := yulState.toMachineState.lookupMemoryRange poz len
            let s : List UInt8 := toBytesBigEndian ζ
            let a₀ : List UInt8 := [0xff]
            let addr₀ := KEC <| ⟨⟨a₀ ++ this ++ s⟩⟩ ++ KEC code
            let addr : Address := Fin.ofNat <| fromBytesBigEndian addr₀.data.data
            match yulState.toState.accountMap.lookup Iₐ with
              | none => .ok <| (yulState, some 0)
              | some ac_Iₐ =>
                if v < ac_Iₐ.balance then .ok <| (yulState, some 0) else
                let ac_Iₐ' := {ac_Iₐ with balance := ac_Iₐ.balance - v, nonce := ac_Iₐ.nonce + 1}
                let v' :=
                  match yulState.toState.accountMap.lookup addr with
                    | none => 0
                    | some ac_addr => ac_addr.balance
                let newAccount : Account :=
                  { nonce := 1
                  , balance := v + v'
                  , code := code
                  , codeHash := fromBytesBigEndian (KEC code).data.data
                  , storage := default
                  , tstorage := default
                  }
                let yulState' :=
                  yulState.setState <|
                    yulState.toState.updateAccount addr newAccount
                      |>.updateAccount Iₐ ac_Iₐ'

                .ok <| (yulState', some addr)
          | _ => .error .InvalidArguments

    | _, _ => sorry

example :
  (RLP (.𝔹 (toBytesBigEndian 123456789).toByteArray) |>.map toHex) == some "84075bcd15"
:= by native_decide

example :
  RLP (.𝔹 .empty) == ByteArray.mk #[0x80]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x78])) == ByteArray.mk #[0x78]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x80])) == ByteArray.mk #[0x81, 0x80]
:= by  native_decide

example :
  RLP (.𝔹 (ByteArray.mk #[0x83])) == ByteArray.mk #[0x81, 0x83]
:= by  native_decide

private def fiftyFiveBytes : List UInt8 := List.replicate 55 0x83
example :
  RLP (.𝔹 ⟨⟨fiftyFiveBytes⟩⟩) == some ⟨⟨0xB7 :: fiftyFiveBytes⟩⟩
:= by  native_decide

-- private def largeBytes : List UInt8 := List.replicate (2^20) 0x83
-- example :
--   RLP (.𝔹 ⟨⟨largeBytes⟩⟩) == some ⟨⟨0xBA :: 0x10 :: 0x00 :: 0x00 :: largeBytes⟩⟩
-- := by  native_decide

example :
  RLP (.𝔹 (BE 0)) == ByteArray.mk #[0x80]
:= by  native_decide

example :
  RLP (.𝔹 (BE 255)) == ByteArray.mk #[0x81, 0xff]
:= by  native_decide

example :
  RLP (.𝕃 []) == ByteArray.mk #[0xC0]
:= by native_decide

private def hello : Array UInt8 := #[104, 101, 108, 108, 111]
private def how : Array UInt8 := #[104, 111, 119]
private def are : Array UInt8 := #[97, 114, 101]
private def you : Array UInt8 := #[121, 111, 117]
private def doing : Array UInt8 := #[100, 111, 105, 110, 103]

example :
  RLP (.𝕃 [.𝔹 (ByteArray.mk hello)]) ==
    ByteArray.mk (#[0xC6, 0x85] ++ hello)
:= by  native_decide

example :
  RLP (.𝕃 [.𝔹 (BE 255)]) == ByteArray.mk #[0xC2, 0x81, 0xff]
:= by  native_decide

example :
  RLP (.𝕃 (List.replicate 5 (.𝔹 ⟨hello⟩) ++ List.replicate 5 (.𝔹 (BE 35))))
    ==
  ByteArray.mk
    ( #[0xE3]
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[35, 35, 35, 35, 35]
    )
:= by native_decide

example :
  RLP (.𝕃 (List.replicate 10 (.𝔹 (BE 35)) ++ List.replicate 10 (.𝔹 ⟨hello⟩)))
    ==
  ByteArray.mk
    ( #[0xF8] ++ #[70]
      ++ #[35, 35, 35, 35, 35, 35, 35, 35, 35, 35]
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
      ++ #[0x85] ++ hello
    )
:= by native_decide

private def nestedSequence : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝔹 ⟨you⟩, .𝕃 [.𝔹 ⟨doing⟩]]]
    ]

example :
  RLP nestedSequence
    ==
  ByteArray.mk
    ( #[0xdd, 0x85]
      ++ hello
      ++ #[0x81,0xff,0xd4,0x83]
      ++ how
      ++ #[0xcf,0x83]
      ++ are
      ++ #[0x83]
      ++ you
      ++ #[0xc6, 0x85]
      ++ doing
      )
:= by native_decide

private def willFail₁ : 𝕋 := .𝔹 (BE 123)
private def willFail₂ : 𝕋 :=
  .𝕃
    [ .𝔹 ⟨hello⟩
    , .𝔹 (BE 255)
    , .𝕃 [.𝔹 ⟨how⟩, .𝕃 [.𝔹 ⟨are⟩, .𝕃 [.𝔹 ⟨you⟩, .𝔹 (BE 123)]]]
    ]

end Semantics

end EvmYul
