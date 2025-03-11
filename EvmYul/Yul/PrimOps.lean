import EvmYul.Yul.State
import EvmYul.Yul.Exception
import EvmYul.Yul.StateOps
import EvmYul.SharedStateOps

import EvmYul.UInt256

import EvmYul.Wheels

namespace EvmYul

namespace Yul

open Lean Parser

set_option autoImplicit true

def Transformer := Yul.State → List Literal → Except Yul.Exception (Yul.State × Option Literal)

def execUnOp (f : Primop.Unary) : Transformer
  | s, [a] => .ok (s, f a)
  | _, _   => throw .InvalidArguments

def execBinOp (f : Primop.Binary) : Transformer
  | s, [a, b] => .ok (s, f a b)
  | _, _      => throw .InvalidArguments

def execTriOp (f : Primop.Ternary) : Transformer
  | s, [a, b, c] => .ok (s, f a b c)
  | _, _         => throw .InvalidArguments

def execQuadOp (f : Primop.Quaternary) : Transformer
  | s, [a, b, c, d] => .ok (s, f a b c d)
  | _, _            => throw .InvalidArguments

def executionEnvOp (op : ExecutionEnv → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.executionEnv)

def unaryExecutionEnvOp (op : ExecutionEnv → UInt256 → UInt256) : Transformer :=
  λ yulState lits ↦
    match lits with
    | [a] => .ok (yulState, .some <| op yulState.executionEnv a)
    | _ => .error .InvalidArguments

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toMachineState)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let mState' := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let (val, mState') := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', some val)
    | _ => .error .InvalidArguments

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let mState' := op yulState.toMachineState a b c
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def binaryStateOp
  (op : EvmYul.State → UInt256 → UInt256 → EvmYul.State) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let state' := op yulState.toState a b
      let yulState' := yulState.setState state'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def stateOp (op : EvmYul.State → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toState)

def unaryStateOp (op : EvmYul.State → UInt256 → EvmYul.State × UInt256) : Transformer :=
  λ yulState lits ↦
      match lits with
        | [lit] =>
          let (state', b) := op yulState.toState lit
          let yulState' :=
            yulState.setSharedState { yulState.toSharedState with toState := state' }
          .ok (yulState', some b)
        | _ => .error .InvalidArguments

def ternaryCopyOp (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let sState' := op yulState.toSharedState a b c
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

def quaternaryCopyOp
  (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c, d] =>
      let sState' := op yulState.toSharedState a b c d
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

private def yulLogOp (yulState : State) (a b : UInt256) (t : Array UInt256) : State × Option Literal :=
  let sharedState' := SharedState.logOp a b t yulState.toSharedState
  ( yulState.setSharedState sharedState'
  , none
  )

def log0Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b] =>
        .ok <| yulLogOp yulState a b #[]
      | _ => .ok (yulState, none)

def log1Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c] =>
        .ok <| yulLogOp yulState a b #[c]
      | _ => .ok (yulState, none)

def log2Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d] =>
        .ok <| yulLogOp yulState a b #[c, d]
      | _ => .ok (yulState, none)

def log3Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e] =>
        .ok <| yulLogOp yulState a b #[c, d, e]
      | _ => .ok (yulState, none)

def log4Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e, f] =>
        .ok <| yulLogOp yulState a b #[c, d, e, f]
      | _ => .ok (yulState, none)

end Yul

end EvmYul
