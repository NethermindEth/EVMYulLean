import EvmYul.Data.Stack

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.StateOps
import EvmYul.SharedStateOps

namespace EvmYul

namespace EVM

def Transformer := EVM.State → Except EVM.Exception EVM.State

def execUnOp (debugMode : Bool) (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.stack.pop with
      | some ⟨stack, μ₀⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀}"
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀)
      | _ =>
        .error <| .ExecutionException .StackUnderflow

def execBinOp (debugMode : Bool) (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ => Id.run do
        let result := f μ₀ μ₁
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
          dbg_trace s!"result: {result}"
        .ok <| s.replaceStackAndIncrPC (stack.push result)
      | _ =>
        .error <| .ExecutionException .StackUnderflow

def execTriOp (debugMode : Bool) (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}"
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂)
      | _ =>
        .error <| .ExecutionException .StackUnderflow

def execQuadOp (debugMode : Bool) (f : Primop.Quaternary) : Transformer :=
  λ s ↦
    match s.stack.pop4 with
      | some ⟨ stack , μ₀ , μ₁ , μ₂, μ₃ ⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂} μ₃: {μ₃}"
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂ μ₃)
      | _ =>
        .error <| .ExecutionException .StackUnderflow

def executionEnvOp (debugMode : Bool) (op : ExecutionEnv → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.executionEnv
    if debugMode then
      dbg_trace s!"result: {result}"
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def unaryExecutionEnvOp (debugMode : Bool) (op : ExecutionEnv → UInt256 → UInt256) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop with
    | some ⟨ s , μ₀⟩ => Id.run do
      let result := op evmState.executionEnv μ₀
      if debugMode then
        dbg_trace s!"result: {result}"
      .ok <|
        evmState.replaceStackAndIncrPC (s.push result)
    | _ => .error <| .ExecutionException .StackUnderflow

def machineStateOp (debugMode : Bool) (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.toMachineState
    if debugMode then dbg_trace s!"got result: {result}"
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def binaryMachineStateOp
  (debugMode : Bool)
  (op : MachineState → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      if debugMode then
        dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
      let mState' := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error <| .ExecutionException .StackUnderflow

def binaryMachineStateOp'
  (debugMode : Bool)
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      if debugMode then
        dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
      let (val, mState') := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error <| .ExecutionException .StackUnderflow

def ternaryMachineStateOp
  (debugMode : Bool)
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ s , μ₀, μ₁, μ₂ ⟩ => Id.run do
      if debugMode then
        dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}"
      let mState' := op evmState.toMachineState μ₀ μ₁ μ₂
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error <| .ExecutionException .StackUnderflow

def binaryStateOp
  (debugMode : Bool)
  (op : EvmYul.State → UInt256 → UInt256 → EvmYul.State)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      if debugMode then
        dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
      let state' := op evmState.toState μ₀ μ₁
      let evmState' := {evmState with toState := state'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error <| .ExecutionException .StackUnderflow

def stateOp (debugMode : Bool) (op : EvmYul.State → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    if debugMode then dbg_trace s!"got result: {op evmState.toState}";
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toState)

def unaryStateOp
  (debugMode : Bool)
  (op : EvmYul.State → UInt256 → EvmYul.State × UInt256)
    :
  Transformer
:= λ evmState ↦
      match evmState.stack.pop with
        | some ⟨stack' , μ₀ ⟩ => Id.run do
          if debugMode then
            dbg_trace s!"called with μ₀: {μ₀}"
          let (state', b) := op evmState.toState μ₀
          let evmState' := {evmState with toState := state'}
          if debugMode then dbg_trace s!"got result: {b}"
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error <| .ExecutionException .StackUnderflow

def ternaryCopyOp
  (debugMode : Bool)
  (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ stack' , μ₀, μ₁, μ₂⟩ => Id.run do
      if debugMode then
        dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}"
      let sState' := op evmState.toSharedState μ₀ μ₁ μ₂
      let evmState' := { evmState with toSharedState := sState'}
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error <| .ExecutionException .StackUnderflow

def quaternaryCopyOp
  (debugMode : Bool)
  (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState)
    :
  Transformer
:=  λ evmState ↦
      match evmState.stack.pop4 with
        | some ⟨ stack' , μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
          if debugMode then
            dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂} μ₃: {μ₃}"
          let sState' := op evmState.toSharedState μ₀ μ₁ μ₂ μ₃
          let evmState' := { evmState with toSharedState := sState'}
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error <| .ExecutionException .StackUnderflow

private def evmLogOp (evmState : State) (μ₀ μ₁ : UInt256) (t : List UInt256) : State :=
  let sharedState' := SharedState.logOp μ₀ μ₁ t evmState.toSharedState
  { evmState with toSharedState := sharedState'}

def log0Op (debugMode : Bool) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop2 with
      | some ⟨stack', μ₀, μ₁⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
        let evmState' := evmLogOp evmState μ₀ μ₁ []
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error <| .ExecutionException .StackUnderflow

def log1Op (debugMode : Bool) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error <| .ExecutionException .StackUnderflow

def log2Op (debugMode : Bool) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop4 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}  μ₃: {μ₃}"
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error <| .ExecutionException .StackUnderflow

def log3Op (debugMode : Bool) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop5 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}  μ₃: {μ₃} μ₄: {μ₄}"
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error <| .ExecutionException .StackUnderflow

def log4Op (debugMode : Bool) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop6 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ => Id.run do
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}  μ₃: {μ₃} μ₄: {μ₄} μ₅: {μ₅}"
        let evmState' := evmLogOp evmState μ₀ μ₁ [μ₂, μ₃, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error <| .ExecutionException .StackUnderflow

end EVM

end EvmYul
