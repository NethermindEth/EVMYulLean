import EvmYul.Data.Stack

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.StateOps
import EvmYul.SharedStateOps

namespace EvmYul

namespace EVM

def Transformer := EVM.State → Except EVM.Exception EVM.State

def execUnOp (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.stack.pop with
      | some ⟨stack, μ₀⟩ =>
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀)
      | _ =>
        .error .InvalidStackSizeException

def execBinOp (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ =>
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁)
      | _ =>
        .error .InvalidStackSizeException

def execTriOp (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂)
      | _ =>
        .error .InvalidStackSizeException

def execQuadOp (f : Primop.Quaternary) : Transformer :=
  λ s ↦
    match s.stack.pop4 with
      | some ⟨ stack , μ₀ , μ₁ , μ₂, μ₃ ⟩ =>
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂ μ₃)
      | _ =>
        .error .InvalidStackSizeException

def executionEnvOp (op : ExecutionEnv → UInt256) : Transformer :=
  λ evmState ↦
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.executionEnv)

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toMachineState)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState) : Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ =>
      let mState' := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error EVM.Exception.InvalidStackSizeException

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) : Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ =>
      -- dbg_trace s!"keccak with μ₀: {μ₀} μ₁: {μ₁}"
      let (val, mState') := op evmState.toMachineState μ₀ μ₁
      -- dbg_trace s!"op; val: {val} "
      let evmState' := {evmState with toMachineState := mState'}
      -- let evmState' := evmState
      -- let val := 4
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error EVM.Exception.InvalidStackSizeException

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) : Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ s , μ₀, μ₁, μ₂ ⟩ =>
      let mState' := op evmState.toMachineState μ₀ μ₁ μ₂
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error EVM.Exception.InvalidStackSizeException

def binaryStateOp
  (op : EvmYul.State → UInt256 → UInt256 → EvmYul.State) : Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ =>
      let state' := op evmState.toState μ₀ μ₁
      let evmState' := {evmState with toState := state'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error EVM.Exception.InvalidStackSizeException

def stateOp (op : EvmYul.State → UInt256) : Transformer :=
  λ evmState ↦
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toState)

def unaryStateOp (op : EvmYul.State → UInt256 → EvmYul.State × UInt256) : Transformer :=
  λ evmState ↦
      match evmState.stack.pop with
        | some ⟨stack' , μ₀ ⟩ =>
          let (state', b) := op evmState.toState μ₀
          let evmState' := {evmState with toState := state'}
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error EVM.Exception.InvalidStackSizeException

def ternaryCopyOp (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ stack' , μ₀, μ₁, μ₂⟩ =>
      let sState' := op evmState.toSharedState μ₀ μ₁ μ₂
      let evmState' := { evmState with toSharedState := sState'}
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error EVM.Exception.InvalidStackSizeException

def quaternaryCopyOp
  (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:=  λ evmState ↦
      match evmState.stack.pop4 with
        | some ⟨ stack' , μ₀, μ₁, μ₂, μ₃⟩ =>
          let sState' := op evmState.toSharedState μ₀ μ₁ μ₂ μ₃
          let evmState' := { evmState with toSharedState := sState'}
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error EVM.Exception.InvalidStackSizeException

private def evmLogOp (evmState : State) (μ₀ μ₁ : UInt256) (t : List UInt256) : State :=
  let (substate', μᵢ') := SharedState.logOp μ₀ μ₁ t evmState.toSharedState
  { evmState with substate := substate', maxAddress := μᵢ' }

def log0Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop2 with
      | some ⟨stack', μ₀, μ₁⟩ =>
        let evmState' := evmLogOp evmState μ₀ μ₁ []
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error EVM.Exception.InvalidStackSizeException

def log1Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error EVM.Exception.InvalidStackSizeException

def log2Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop4 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃⟩ =>
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error EVM.Exception.InvalidStackSizeException

def log3Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop5 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄⟩ =>
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error EVM.Exception.InvalidStackSizeException

def log4Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop6 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ =>
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error EVM.Exception.InvalidStackSizeException

end EVM

end EvmYul
