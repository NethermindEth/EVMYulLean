import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.YPState

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Semantics
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256

import Conform.Wheels

open EvmYul.DebuggingAndProfiling

namespace EvmYul

namespace EVM

def argOnNBytesOfInstr : Operation .EVM → ℕ
  -- | .Push .PUSH0 => 0 is handled as default.
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def N (pc : UInt256) (instr : Operation .EVM) := pc + ⟨1⟩ + .ofNat (argOnNBytesOfInstr instr)

-- /--
-- Computes `μᵢ'`, i.e. the maximum memory touched by `instr`.
-- -/
-- def maxMemoryOfInstr (old : μᵢ) (stack : Stack UInt256) (instr : Operation .EVM) : Except EVM.Exception UInt256 :=
--   match instr with
--     | .KECCAK256 => _ -- YP: M (μi, μs[0], μs[1])
--     | _ => _

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt256) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  -- dbg_trace s!"DECODING; arr: {arr} pc: {pc}"
  -- let wagh := arr.get? pc
  -- dbg_trace s!"wagh is: {wagh}"
  let instr ← arr.get? pc.toNat >>= EvmYul.EVM.parseInstr
  let argWidth := argOnNBytesOfInstr instr
  -- dbg_trace s!"pc: {pc}; Decoded: {instr.pretty}; argWidth={argWidth}"
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (EvmYul.uInt256OfByteArray (arr.extract' pc.toNat.succ (pc.toNat.succ + argWidth)), argWidth)
  )

def fetchInstr (I : EvmYul.ExecutionEnv) (pc : UInt256) :
               Except EVM.Exception (Operation .EVM × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .InvalidStackSizeException) Except.ok

partial def D_J (c : ByteArray) (i : UInt256) : List UInt256 :=
  match c.get? i.toNat >>= EvmYul.EVM.parseInstr with
    | none => []
    | some cᵢ =>
      if  cᵢ = .JUMPDEST then
        i :: D_J c (N i cᵢ)
      else
        D_J c (N i cᵢ)

private def BitVec.ofFn {k} (x : Fin k → Bool) : BitVec k :=
  BitVec.ofNat k (natOfBools (Vector.ofFn x))
  where natOfBools (vec : Vector Bool k) : Nat :=
          (·.1) <| vec.toList.foldl (init := (0, 0)) λ (res, i) bit ↦ (res + 2^i * bit.toNat, i + 1)

def byteAt (μ₀ μ₁ : UInt256) : UInt256 :=
  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < ⟨32⟩
                                             then v₁.getLsb i
                                             else false)
  EvmYul.UInt256.ofNat (BitVec.toNat vᵣ)

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error EVM.Exception.InvalidStackSizeException

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error EVM.Exception.InvalidStackSizeException

local instance : MonadLift Option (Except EVM.Exception) :=
  ⟨Option.option (.error .InvalidStackSizeException) .ok⟩

mutual

def call (debugMode : Bool) (fuel : Nat)
  (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (state : SharedState)
    :
  Except EVM.Exception (UInt256 × SharedState)
:= do
  match fuel with
    | 0 => dbg_trace "nofuel"; .ok (⟨1⟩, state)
    | .succ f =>
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let (i, newMachineState) := state.toMachineState.readBytes inOffset inSize.toNat
      -- t ≡ μs[1] mod 2^160
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := state.executionEnv.codeOwner
      let σ := state.accountMap
      let Iₑ := state.executionEnv.depth
      let callgas := Ccallgas t value gas σ state.toMachineState state.substate
      let (cA, σ', g', A', z, o) ← do
        -- TODO - Refactor condition and possibly share with CREATE
        if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ Account.balance) ∧ Iₑ < 1024 then
          let A' := state.addAccessedAccount t |>.substate -- A' ≡ A except A'ₐ ≡ Aₐ ∪ {t}
          let resultOfΘ ←
            Θ (debugMode := debugMode)
              (fuel := f)
              blobVersionedHashes
              (createdAccounts := state.createdAccounts)
              (σ  := σ)                             -- σ in  Θ(σ, ..)
              (A  := A')                            -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := state.executionEnv.sender)     -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat state.executionEnv.gasPrice)   -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := state.executionEnv.header)
              (w  := permission)                    -- I_w in Θ(.., I_W)
          pure resultOfΘ
          else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
          .ok
            (state.createdAccounts, state.toState.accountMap, .ofNat callgas, state.toState.substate, false, .some .empty)
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (o.elim ⟨0⟩ (UInt256.ofNat ∘ ByteArray.size))

      -- TODO - Check what happens when `o = .none`.
      let μ'ₘ := newMachineState.writeBytes (o.getD .empty) outOffset n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      let μ'_g := μ'ₘ.gasAvailable + g' -- Ccall is subtracted in X as part of C

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.find? state.executionEnv.codeOwner |>.elim ⟨0⟩ Account.balance) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := state.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
      let μ'incomplete : MachineState :=
        { μ'ₘ with
            returnData   := μ'ₒ.getD .empty -- TODO - Check stuff wrt. .none
            gasAvailable := μ'_g
        }

      let result : SharedState := { state with accountMap := σ', substate := A', createdAccounts := cA }
      let result := {
        result with toMachineState := μ'incomplete
      }
      .ok (x, result)

def step (debugMode : Bool) (fuel : ℕ) (instr : Option (Operation .EVM × Option (UInt256 × Nat)) := .none) : EVM.Transformer :=
  match fuel with
    | 0 => .ok
    | .succ f =>
    λ (evmState : EVM.State) ↦ do
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    let (instr, arg) ←
      match instr with
        | .none => fetchInstr evmState.toState.executionEnv evmState.pc
        | .some (instr, arg) => pure (instr, arg)
    if
      debugMode &&
        (instr.isPush || instr.isJump || instr.isPC || instr.isJumpdest || instr.isDup || instr.isSwap || instr.isCreate || instr.isCall)
    then
        dbg_trace instr.pretty
    let evmState := { evmState with execLength := evmState.execLength + 1 }
    match instr with
      | .Push .PUSH0 =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push ⟨0⟩)
      | .Push _ => do
        let some (arg, argWidth) := arg | .error EVM.Exception.InvalidStackSizeException
        if debugMode then
          dbg_trace s!"called with {arg} | 0x{padLeft (2*argWidth) <| toHex (BE arg.toNat)}"
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
      | .JUMP =>
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            if debugMode then
              dbg_trace s!"called with μ₀: {μ₀}"
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error EVM.Exception.InvalidStackSizeException
      | .JUMPI =>
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            if debugMode then
              dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁}"
            let newPc :=
            if μ₁ != ⟨0⟩ then
              -- dbg_trace s!"jumped to {μ₀}"
              μ₀
            else
              evmState.pc + ⟨1⟩
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error EVM.Exception.InvalidStackSizeException
      | .PC =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
      | .JUMPDEST =>
        .ok evmState.incrPC

      | .DUP1 => dup 1 evmState
      | .DUP2 => dup 2 evmState
      | .DUP3 => dup 3 evmState
      | .DUP4 => dup 4 evmState
      | .DUP5 => dup 5 evmState
      | .DUP6 => dup 6 evmState
      | .DUP7 => dup 7 evmState
      | .DUP8 => dup 8 evmState
      | .DUP9 => dup 9 evmState
      | .DUP10 => dup 10 evmState
      | .DUP11 => dup 11 evmState
      | .DUP12 => dup 12 evmState
      | .DUP13 => dup 13 evmState
      | .DUP14 => dup 14 evmState
      | .DUP15 => dup 15 evmState
      | .DUP16 => dup 16 evmState

      | .SWAP1 => swap 1 evmState
      | .SWAP2 => swap 2 evmState
      | .SWAP3 => swap 3 evmState
      | .SWAP4 => swap 4 evmState
      | .SWAP5 => swap 5 evmState
      | .SWAP6 => swap 6 evmState
      | .SWAP7 => swap 7 evmState
      | .SWAP8 => swap 8 evmState
      | .SWAP9 => swap 9 evmState
      | .SWAP10 => swap 10 evmState
      | .SWAP11 => swap 11 evmState
      | .SWAP12 => swap 12 evmState
      | .SWAP13 => swap 13 evmState
      | .SWAP14 => swap 14 evmState
      | .SWAP15 => swap 15 evmState
      | .SWAP16 => swap 16 evmState
      | .CREATE =>
        match evmState.stack.pop3 with
          | some ⟨stack, μ₀, μ₁, μ₂⟩ => do
            if debugMode then
              dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂}"
            let (i, newMachineState) := evmState.toMachineState.readBytes μ₁ μ₂.toNat
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

            let Λ :=
              Lambda debugMode f
                evmState.executionEnv.blobVersionedHashes
                evmState.createdAccounts
                σStar
                evmState.toState.substate
                Iₐ
                Iₒ
                (.ofNat <| L evmState.gasAvailable.toNat)
                (.ofNat I.gasPrice)
                μ₀
                i
                (.ofNat <| Iₑ + 1)
                ζ
                I.header
                I.perm
            let (a, evmState', g', z, o)
                  : (AccountAddress × EVM.State × UInt256 × Bool × ByteArray)
              :=
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ Account.balance) ∧ Iₑ < 1024 then
                match Λ with
                  | some (a, cA, σ', g', A', z, o) =>
                    ( a
                    , { evmState with
                          accountMap := σ'
                          substate := A'
                          createdAccounts := cA
                      }
                    , g'
                    , z
                    , o
                    )
                  | none => (0, evmState, ⟨0⟩, False, .empty)
              else
                (0, evmState, ⟨0⟩, False, .empty)
            let x : UInt256 :=
              let balance := σ.find? a |>.option ⟨0⟩ Account.balance
                if z = false ∨ Iₑ = 1024 ∨ μ₀ < balance then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState'.gasAvailable + g').toNat < L (evmState'.gasAvailable.toNat) then
              .error .OutOfGass
            let evmState' :=
              {evmState' with
                toMachineState :=
                  { newMachineState with
                      returnData := newReturnData
                      gasAvailable :=
                        .ofNat <| evmState'.gasAvailable.toNat - L (evmState'.gasAvailable.toNat) + g'.toNat
                  }
              }
            .ok <| evmState'.replaceStackAndIncrPC (evmState.stack.push x)
          | _ =>
          .error .InvalidStackSizeException
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            if debugMode then
              dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} μ₂: {μ₂} μ₃: {μ₃}"
            let (i, newMachineState) := evmState.toMachineState.readBytes μ₁ μ₂.toNat
            let ζ := EvmYul.UInt256.toByteArray μ₃
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
            let Λ :=
              Lambda debugMode f
                evmState.executionEnv.blobVersionedHashes
                evmState.createdAccounts
                σStar
                evmState.toState.substate
                Iₐ
                Iₒ
                (.ofNat <| L evmState.gasAvailable.toNat)
                (.ofNat I.gasPrice)
                μ₀
                i
                (.ofNat <| Iₑ + 1)
                ζ
                I.header
                I.perm
            let (a, evmState', g', z, o) : (AccountAddress × EVM.State × UInt256 × Bool × ByteArray) :=
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ Account.balance) ∧ Iₑ < 1024 then
                match Λ with
                  | some (a, cA, σ', g', A', z, o) =>
                    (a, {evmState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
                  | none => (0, evmState, ⟨0⟩, False, .empty)
              else
                (0, evmState, ⟨0⟩, False, .empty)
            let x : UInt256 :=
              let balance := σ.find? a |>.option ⟨0⟩ Account.balance
                if z = false ∨ Iₑ = 1024 ∨ μ₀ < balance then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState'.gasAvailable + g').toNat < L (evmState'.gasAvailable).toNat then
              .error .OutOfGass
            let evmState' :=
              {evmState' with
                toMachineState :=
                  { newMachineState with
                      returnData := newReturnData
                      gasAvailable := .ofNat <| evmState'.gasAvailable.toNat - L (evmState'.gasAvailable.toNat) + g'.toNat
                  }
              }
            .ok <| evmState'.replaceStackAndIncrPC (evmState.stack.push x)
          | _ =>
          .error .InvalidStackSizeException
      -- TODO: Factor out the semantics for `CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} ({toHex μ₁.toByteArray |>.takeRight 5}) μ₂: {μ₂} μ₃: {μ₃} μ₄: {μ₄} μ₅: {μ₅} μ₆: {μ₆}"
        let (x, state') ←
          call debugMode f evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState.toSharedState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' :=
          { evmState with toSharedState := state'}.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .CALLCODE =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} ({toHex μ₁.toByteArray |>.takeRight 5}) μ₂: {μ₂} μ₃: {μ₃} μ₄: {μ₄} μ₅: {μ₅} μ₆: {μ₆}"
        let (x, state') ←
          call debugMode f evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState.toSharedState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' :=
          { evmState with toSharedState := state'}.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .DELEGATECALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        -- TODO: Use indices correctly
        let (stack, μ₀, μ₁, /-μ₂,-/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} ({toHex μ₁.toByteArray |>.takeRight 5}) μ₂: {μ₃} μ₃: {μ₄} μ₄: {μ₅} μ₅: {μ₆}"
        let (x, state') ←
          call debugMode f evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState.toSharedState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' :=
          { evmState with toSharedState := state'}.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STATICCALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /- μ₂, -/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        if debugMode then
          dbg_trace s!"called with μ₀: {μ₀} μ₁: {μ₁} ({toHex μ₁.toByteArray |>.takeRight 5}) μ₂: {μ₃} μ₃: {μ₄} μ₄: {μ₅} μ₅: {μ₆}"
        let (x, state') ←
          call debugMode f evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState.toSharedState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' :=
          { evmState with toSharedState := state'}.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | instr => EvmYul.step debugMode instr evmState

/--
  Iterative progression of `step`
-/
def X (debugMode : Bool) (fuel : ℕ) (evmState : State) : Except EVM.Exception (State × Option ByteArray) := do
  match fuel with
    | 0 => .ok (evmState, some .empty)
    | .succ f =>
      let I_b := evmState.toState.executionEnv.code
      let instr@(w, _) := decode I_b evmState.pc |>.getD (.STOP, .none)
      -- dbg_trace s!"gas available in X {evmState.gasAvailable} for {w.pretty}"

      -- (159)
      let W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
        w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4] ∨
        (w = .CALL ∧ s.get? 2 ≠ some ⟨0⟩)

      -- Exceptional halting (158)
      let Z : Bool := Id.run do
        let Z₀ := δ w = none
        let Z₁ := evmState.stack.length < (δ w).getD 0
        let Z₂ := w = .JUMP ∧ notIn (evmState.stack.get? 0) (D_J I_b ⟨0⟩)
        let Z₃ := w = .JUMPI ∧ (evmState.stack.get? 1 ≠ some ⟨0⟩) ∧ notIn (evmState.stack.get? 0) (D_J I_b ⟨0⟩)
        let Z₄ := w = .RETURNDATACOPY ∧ evmState.stack.getD 1 ⟨0⟩ + evmState.stack.getD 2 ⟨0⟩ > .ofNat evmState.returnData.size
        let Z₅ := evmState.stack.length - (δ w).getD 0 - (α w).getD 0 > 1024
        let Z₆ := (¬ evmState.executionEnv.perm) ∧ W w evmState.stack
        if Z₀ ∧ debugMode then
          dbg_trace s!"Exceptional halting: invalid operation {w.pretty} has δ = ∅"
        if Z₁ ∧ debugMode then
          dbg_trace s!"Exceptional halting: insufficient stack items for {w.pretty}"
        if Z₂ ∧ debugMode then
          dbg_trace s!"Exceptional halting: invalid JUMP destination"
        if Z₃ ∧ debugMode then
          dbg_trace s!"Exceptional halting: invalid JUMPI destination"
        if Z₄ ∧ debugMode then
          dbg_trace s!"Exceptional halting: not enough output data for RETURNDATACOPY: required {evmState.stack.getD 1 ⟨0⟩ + evmState.stack.getD 2 ⟨0⟩} bytes but got {evmState.returnData.size}"
        if Z₅ ∧ debugMode then
          dbg_trace s!"Exceptional halting: {w.pretty} would result in stack larger than 1024 elements"
        if Z₆ ∧ debugMode then
          dbg_trace s!"Exceptional halting: attempted {w.pretty} without permission"
        pure (Z₀ ∨ Z₁ ∨ Z₂ ∨ Z₃ ∨ Z₄ ∨ Z₅ ∨ Z₆)

      let H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          -- dbg_trace s!"{w.pretty} gives {toHex μ.H_return}"
          some <| μ.H_return
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none

      if Z then
        -- dbg_trace "exceptional halting"
        .ok ({evmState with accountMap := ∅}, none)
      -- else
        -- TODO - Probably an exceptional gas scenario, as we should have technically checked apriori.
        -- if w = .REVERT then
          -- The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
          -- but we actually have to call the semantics of `REVERT` to pass the test
          -- EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
          -- And the EEL spec does so too.
          -- .ok ({evmState with accountMap := ∅}, .some evmState.returnData)
        else
          -- NB we still need to check gas, because `Z` needs to call `C`, which needs `μ'ᵢ`.
          -- We first call `step` to obtain `μ'ᵢ`, which we then use to compute `C`.
          let evmState' ← step debugMode f instr evmState
          -- if w == .DELEGATECALL then
          --   dbg_trace s!"gas available after step DELEGATECALL {evmState'.gasAvailable}"
          -- NB: (327)
          -- w := if pc < I.code.size
          --      then match EVM.decode I.code pc with
          --             | .none => .STOP
          --             | .some instr => instr
          --      else .STOP
          -- Is not necessary - we have already decoded the instruction,
          -- and computing with a default `.STOP` that costs 0 is not necessary.
          -- Maybe we should restructure in a way such that it is more meaningful to compute
          -- gas independently, but the model has not been set up thusly and it seems
          -- that neither really was the YP.
          -- Similarly, we cannot reach a situation in which the stack elements are not available
          -- on the stack because this is guarded above. As such, `C` can be pure here.
          let gasCost ← C evmState evmState'.activeWords w
          -- dbg_trace s!"gasAvailable: {evmState.gasAvailable}; gasCost: {gasCost} for instruction {w.pretty}"
          if debugMode && evmState.gasAvailable.toNat < gasCost then
            dbg_trace s!"gasAvailable: {evmState.gasAvailable} < gasCost: {gasCost} for instruction {w.pretty}"
          if evmState.gasAvailable.toNat < gasCost then do
            -- Out of gas. This is a part of `Z`, as such, we have the same return value.
            -- dbg_trace "Out of gass!"
            -- dbg_trace s!"gas available: {evmState.gasAvailable}; gas cost: {gasCost}"
            .ok ({evmState with accountMap := ∅}, none)
          else do
            let evmState' := {evmState' with gasAvailable := evmState'.gasAvailable - .ofNat gasCost}
            -- dbg_trace s!"new gas available after {w.pretty}: {evmState.gasAvailable - gasCost}"
            -- dbg_trace s!"gas cost after {w.pretty}: {gasCost}"
            match H evmState'.toMachineState w with -- The YP does this in a weird way.
              -- NB in our model, we need the max memory touched of the executed instruction
              -- before we can check whether there is enough gas to execute the instruction.
              -- It might turn out to be the case that we need to separate these two
              -- and compute just the `maxMemory` before doing 'full execution', then check
              -- the gas cost and only then execute, I am unsure as of right now.
              -- Interestingly, the YP is defining `C` with parameters that are much 'broader'
              -- than what is strictly necessary, e.g. we are decoding an instruction, instead of getting one in input.
              | none => X debugMode f evmState'
              | some o =>
                if w == .REVERT then
                  -- The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
                  -- but we actually have to call the semantics of `REVERT` to pass the test
                  -- EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
                  -- And the EEL spec does so too.
                  .ok <| ({evmState' with accountMap := ∅}, some o)
                else
                  .ok <| (evmState', some o)
 where
  belongs (o : Option UInt256) (l : List UInt256) : Bool :=
    match o with
      | none => false
      | some n => l.contains n
  notIn (o : Option UInt256) (l : List UInt256) : Bool := not (belongs o l)

/--
  The code execution function
-/
def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (debugMode : Bool)
  (fuel : ℕ)
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (σ : YPState)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv)
    :
  Except EVM.Exception (Batteries.RBSet AccountAddress compare × YPState × UInt256 × Substate × Option ByteArray)
:= do
  match fuel with
    | 0 => .ok (createdAccounts, σ, g, A, some .empty) -- TODO - Gas model
    | .succ f =>
      let defState : EVM.State := default
      let freshEvmState : EVM.State :=
        { defState with
            accountMap := σ
            executionEnv := I
            substate := A
            createdAccounts := createdAccounts
            gasAvailable := g
        }
      let (evmState', o) ← X debugMode f freshEvmState
      -- if debugMode then
      -- dbg_trace s!"Ξ executed {evmState'.execLength} primops"
      let finalGas := evmState'.gasAvailable -- TODO(check): Do we need to compute `C` here one more time?
      return (evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate, o)

def Lambda
  (debugMode : Bool)
  (fuel : ℕ)
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare) -- needed for EIP-6780
  (σ : YPState)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)  -- available gas
  (p : UInt256)   -- gas price
  (v : UInt256)   -- endowment
  (i : ByteArray) -- the initialisation EVM code
  (e : UInt256)   -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader) -- "I_H has no special treatment and is determined from the blockchain"
  (w : Bool)      -- permission to make modifications to the state
  :
  Option
    ( AccountAddress
    × Batteries.RBSet AccountAddress compare
    × YPState
    × UInt256
    × Substate
    × Bool
    × ByteArray
    )
:=
  match fuel with
    | 0 => dbg_trace "nofuel"; .none
    | .succ f => do

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860
  let MAX_CODE_SIZE := 24576
  let MAX_INITCODE_SIZE := 2 * MAX_CODE_SIZE
  let FORK_BLKNUM := 2675000
  if H.number ≥ FORK_BLKNUM ∧ i.size > MAX_INITCODE_SIZE
    -- TODO: "similar to transactions considered invalid for not meeting the intrinsic gas cost requirement"
    then
      dbg_trace s!"Contract creation failed acording to EIP-3860: {H.number} ≥ {FORK_BLKNUM}"
      none

  let n : UInt256 := (σ.find? s |>.option ⟨0⟩ Account.nonce) - ⟨1⟩
  -- dbg_trace s!"s: {toHex (BE s)}, n:{n}, ζ:{ζ},\n i:{toHex i}"
  let lₐ ← L_A s n ζ i
  let a : AccountAddress := -- (94) (95)
    (KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |>.data.data |> fromBytesBigEndian |> Fin.ofNat
  -- dbg_trace s!"addr: {toHex a.toByteArray}"
  -- dbg_trace s!"s: {toHex s.toByteArray}"
  -- dbg_trace s!"n: {toHex (BE n)}"
  -- dbg_trace s!"code: {toHex i}"
  let createdAccounts := createdAccounts.insert a

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let v' := -- (102)
    match σ.find? a with
      | none => ⟨0⟩
      | some ac => ac.balance

  let newAccount : Account :=
    { nonce := ⟨1⟩
    , balance := v + v'
    , code := .empty
    , storage := default
    , tstorage := default
    , ostorage := default
    }

  -- TODO: (100) What if the sender account does not exist but `v` is non-zero?
  let σStar :=
    match σ.find? s with
      | none => σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , inputData := default
    , code      := i
    , gasPrice  := p.toNat
    , header    := H
    , depth     := e.toNat + 1
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    }
  match Ξ debugMode f createdAccounts σStar g AStar exEnv with -- TODO - Gas model.
    | .error e =>
      if debugMode then
        dbg_trace s!"Ξ failed in contract creation: {repr e}"
      .none
    | .ok (createdAccounts', _, _, _, none) =>
      if debugMode then
        dbg_trace s!"Ξ returned no code in contract creation"
        -- TODO: I think if `o` is `none` at the end of `Ξ` than the `YPState` is necessarily `∅`
        -- because it signifies an exceptional halting.
        -- We could use some refactoring.
      .some (a, createdAccounts', σ, ⟨0⟩, AStar, false, .empty)
    | .ok (createdAccounts', σStarStar, gStarStar, AStarStar, some returnedData) =>
      -- EIP-170 (required for EIP-386):
      -- https://eips.ethereum.org/EIPS/eip-170
      if H.number ≥ FORK_BLKNUM ∧ returnedData.size > MAX_CODE_SIZE
        -- TODO: out of gas error
        then
          if debugMode then
            dbg_trace s!"Contract creation failed acording to EIP-3860: {H.number} ≥ {FORK_BLKNUM}"
          none

      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
            | .none => false
        if debugMode ∧ F₀ then
          dbg_trace "Contract creation failed: account {toHex (BE a)} already existed."
        let F₂ : Bool := gStarStar < .ofNat c
        if debugMode ∧ F₂ then
          dbg_trace "Contract creation failed: g** < c"
        let F₃ : Bool := returnedData.size > 24576
        if debugMode ∧ F₃ then
          dbg_trace "Contract creation failed: code conputed for the new account > 24576"
        let F₄ : Bool := returnedData = ⟨⟨0xef :: returnedData.data.toList.tail⟩⟩
        if debugMode ∧ F₄ then
          dbg_trace "Contract creation failed: code conputed for the new account starts with 0xef"
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
      let fail := F || σStarStar == ∅
      -- (114)
      let g' := if F then ⟨0⟩ else gStarStar - .ofNat c
      -- dbg_trace s!"At the end of Λ : {toHex (BE a)} in σ**: {σStarStar.contains a}"
      let σ' : YPState := -- (115)
        if fail then Id.run do
          -- dbg_trace "Λ fail!"
          σ
        else
          if State.dead σStarStar a then Id.run do
            σStarStar.erase a -- TODO - why was this Finmap.extract that threw away the extracted value? @Andrei
          else
            let newAccount' := σStarStar.findD a default
            σStarStar.insert a {newAccount' with code := returnedData}
      -- (116)
      let A' := if fail then AStar else AStarStar
      -- (117)
      let z := not fail
      .some (a, createdAccounts', σ', g', A', z, returnedData) -- (93)
 where
  L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  := -- (96)
    let s := s.toByteArray
    let n := BE n.toNat
    match ζ with
      | none   => RLP <| .𝕃 [.𝔹 s, .𝔹 n]
      | some ζ => .some <| BE 255 ++ s ++ ζ ++ KEC i

/--
Message cal
`σ`  - evm state
`A`  - accrued substate
`s`  - sender
`o`  - transaction originator
`r`  - recipient
`c`  - the account whose code is to be called, usually the same as `r`
`g`  - available gas
`p`  - effective gas price
`v`  - value
`v'` - value in the execution context
`d`  - input data of the call
`e`  - depth of the message-call / contract-creation stack
`w`  - permissions to make modifications to the stack

TODO check - UInt256 vs Nat for some of the arguments.
TODO check - There's some stuff with .none and .some .empty ByteArray on return.

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
def Θ (debugMode : Bool)
      (fuel : Nat)
      (blobVersionedHashes : List ByteArray)
      (createdAccounts : Batteries.RBSet AccountAddress compare)
      (σ  : YPState)
      (A  : Substate)
      (s  : AccountAddress)
      (o  : AccountAddress)
      (r  : AccountAddress)
      (c  : ToExecute)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Nat)
      (H : BlockHeader)
      (w  : Bool)
        :
      Except EVM.Exception (Batteries.RBSet AccountAddress compare × YPState × UInt256 × Substate × Bool × Option ByteArray)
:=
  -- dbg_trace s!"Θ receiver: {repr r}"
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => do

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != ⟨0⟩ then
          σ.insert r { (default : Account) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- (121) (122) (123)
  let σ₁ ←
    match σ'₁.find? s with
      | none =>
        if v == ⟨0⟩ then
          pure σ'₁
        else
          .error .SenderMustExist
      | some acc =>
        pure <| σ'₁.insert s { acc with balance := acc.balance - v}

  let I : ExecutionEnv :=
    {
      codeOwner := r  -- Equation (132)
      sender    := o  -- Equation (133)
      gasPrice  := p.toNat  -- Equation (134)
      inputData := d  -- Equation (135)
      source    := s  -- Equation (136)
      weiValue  := v' -- Equation (137)
      depth     := e  -- Equation (138)
      perm      := w  -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match c with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := H
      blobVersionedHashes := blobVersionedHashes
    }

  let
    spoon (h : AccountMap × UInt256 × Substate × ByteArray) : Except _ _ :=
      .ok ((∅ : Batteries.RBSet _ _), h.1, h.2.1, h.2.2.1, some h.2.2.2)

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (createdAccounts, σ'', g'', A'', out) ←
    match c with
      | ToExecute.Precompiled p => spoon <|
        match p with
          | 1 => Ξ_ECREC σ₁ g A I
          | 2 => Ξ_SHA256 σ₁ g A I
          | 3 => Ξ_RIP160 σ₁ g A I
          | 4 => Ξ_ID σ₁ g A I
          | 5 => Ξ_EXPMOD σ₁ g A I
          | 6 => Ξ_BN_ADD σ₁ g A I
          | 7 => Ξ_BN_MUL σ₁ g A I
          | 8 => Ξ_SNARKV σ₁ g A I
          | 9 => Ξ_BLAKE2_F σ₁ g A I
          | 10 => Ξ_PointEval σ₁ g A I
          | _ => default
      | ToExecute.Code _ => Ξ debugMode fuel createdAccounts σ₁ g A I

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (128)
  let g' := if σ'' == ∅ && out.isNone then ⟨0⟩ else g''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (130)
  let z := σ'' != ∅

  -- Equation (119)
  .ok (createdAccounts, σ', g', A', z, out)

end

open Batteries (RBMap RBSet)

def checkTransactionGetSender (σ : YPState) (chainId H_f : ℕ) (T : Transaction) (expectedSender : AccountAddress)
  : Except EVM.Exception AccountAddress
:= do
  -- dbg_trace "Transaction: {repr T}"
  let some T_RLP := RLP (← (L_X T)) | .error <| .InvalidTransaction .IllFormedRLP

  let r : ℕ := fromBytesBigEndian T.base.r.data.data
  let s : ℕ := fromBytesBigEndian T.base.s.data.data
  if 0 ≥ r ∨ r ≥ secp256k1n then .error <| .InvalidTransaction .InvalidSignature
  if 0 ≥ s ∨ s > secp256k1n / 2 then .error <| .InvalidTransaction .InvalidSignature
  let v : ℕ := -- (324)
    match T with
      | .legacy t =>
        let w := t.w.toNat
        if w ∈ [27, 28] then
          w - 27
        else
          if w = 35 + chainId * 2 ∨ w = 36 + chainId * 2 then
            (w - 35) % 2 -- `chainId` not subtracted in the Yellow paper but in the EEL spec
          else
            w
      | .access t | .dynamic t | .blob t => t.yParity.toNat
  if v ∉ [0, 1] then .error <| .InvalidTransaction .InvalidSignature

  let h_T := -- (318)
    match T with
      | .legacy _ => KEC T_RLP
      | _ => KEC <| ByteArray.mk #[T.type] ++ T_RLP

  let (S_T : AccountAddress) ← -- (323)
    match ECDSARECOVER h_T (ByteArray.mk #[.ofNat v]) T.base.r T.base.s with
      | .ok s =>
        pure <| Fin.ofNat <| fromBytesBigEndian <|
          ((KEC s).extract 12 32 /- 160 bits = 20 bytes -/ ).data.data
      | .error s => .error <| .SenderRecoverError s
  if S_T != expectedSender then
    .error <| .SenderRecoverError s!"Recovered sender ({toHex S_T.toByteArray}) ≠ expected sender ({toHex expectedSender.toByteArray})"
  -- dbg_trace s!"Looking for S_T: {S_T} in: σ: {repr σ}"

  -- "Also, with a slight abuse of notation ... "
  let (senderCode, senderNonce, senderBalance) :=
    match σ.find? S_T with
      | some sender => (sender.code, sender.nonce, sender.balance)
      | none =>
        dbg_trace s!"could not find sender {toHex S_T.toByteArray}"
        (.empty, ⟨0⟩, ⟨0⟩)


  if senderCode ≠ .empty then .error <| .InvalidTransaction .SenderCodeNotEmpty
  if senderNonce ≠ T.base.nonce then .error <| .InvalidTransaction .InvalidSenderNonce
  let v₀ :=
    match T with
      | .legacy t | .access t => t.gasLimit * t.gasPrice + t.value
      | .dynamic t => t.gasLimit * t.maxFeePerGas + t.value
      | .blob t    => t.gasLimit * t.maxFeePerGas + t.value + (UInt256.ofNat <| (getTotalBlobGas T).getD 0) * t.maxFeePerBlobGas
  -- dbg_trace s!"v₀: {v₀}, senderBalance: {senderBalance}"
  if v₀ > senderBalance then .error <| .InvalidTransaction .UpFrontPayment

  if H_f >
    match T with
      | .dynamic t | .blob t => t.maxFeePerGas.toNat
      | .legacy t | .access t => t.gasPrice.toNat
    then .error <| .InvalidTransaction .BaseFeeTooHigh

  let n :=
    match T.base.recipient with
      | some _ => T.base.data.size
      | none => 0
  if n > 49152 then .error <| .InvalidTransaction .InitCodeDataGreaterThan49152

  match T with
    | .dynamic t =>
      if t.maxPriorityFeePerGas > t.maxFeePerGas then .error <| .InvalidTransaction .InconsistentFees
      pure S_T
    | _ => pure S_T

 where
  L_X (T : Transaction) : Except EVM.Exception 𝕋 := -- (317)
    let accessEntryRLP : AccountAddress × Array UInt256 → 𝕋
      | ⟨a, s⟩ => .𝕃 [.𝔹 (AccountAddress.toByteArray a), .𝕃 (s.map (𝕋.𝔹 ∘ UInt256.toByteArray)).toList]
    let accessEntriesRLP (aEs : List (AccountAddress × Array UInt256)) : 𝕋 :=
      .𝕃 (aEs.map accessEntryRLP)
    match T with
      | /- 0 -/ .legacy t =>
        if t.w.toNat ∈ [27, 28] then
          .ok ∘ .𝕃 ∘ List.map .𝔹 <|
            [ BE t.nonce.toNat -- Tₙ
            , BE t.gasPrice.toNat -- Tₚ
            , BE t.gasLimit.toNat -- T_g
            , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
              t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
            , BE t.value.toNat -- Tᵥ
            , t.data
            ]
        else
          if t.w = .ofNat (35 + chainId * 2) ∨ t.w = .ofNat (36 + chainId * 2) then
            .ok ∘ .𝕃 ∘ List.map .𝔹 <|
              [ BE t.nonce.toNat -- Tₙ
              , BE t.gasPrice.toNat -- Tₚ
              , BE t.gasLimit.toNat -- T_g
              , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
                t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
              , BE t.value.toNat -- Tᵥ
              , t.data -- p
              , BE chainId
              , .empty
              , .empty
              ]
          else
            dbg_trace "IllFormedRLP legacy transacion: Tw = {t.w}; chainId = {chainId}"
            .error <| .InvalidTransaction .IllFormedRLP

      | /- 1 -/ .access t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.gasPrice.toNat) -- Tₚ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- T_v
          , .𝔹 t.data  -- p
          , accessEntriesRLP <| RBSet.toList t.accessList -- T_A
          ]
      | /- 2 -/ .dynamic t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP <| RBSet.toList t.accessList -- T_A
          ]
      | /- 3 -/ .blob t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP <| RBSet.toList t.accessList -- T_A
          , .𝔹 (BE t.maxFeePerBlobGas.toNat)
          , .𝕃 (t.blobVersionedHashes.map .𝔹)
          ]


-- Type Υ using \Upsilon or \GU
def Υ (debugMode : Bool) (fuel : ℕ) (σ : YPState) (chainId H_f : ℕ) (H : BlockHeader) (T : Transaction) (expectedSender : AccountAddress)
  : Except EVM.Exception (YPState × Substate × Bool)
:= do
  let S_T ← checkTransactionGetSender σ chainId H_f T expectedSender
  -- "here can be no invalid transactions from this point"
  let g₀ : ℕ := -- (64)
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
  if T.base.gasLimit.toNat < g₀ then
    .error <| .InvalidTransaction .INTRINSIC_GAS_TOO_LOW
  let senderAccount := (σ.find? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t => t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t => min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
        ostorage := senderAccount.storage -- Needed for `Csstore`.
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList.toList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T |>.insert H.beneficiary |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst).toList compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp}
  let createdAccounts : Batteries.RBSet AccountAddress compare := .empty
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        let (_, _, σ_P, g', A, z, _) :=
          match Lambda debugMode fuel T.blobVersionedHashes createdAccounts σ₀ AStar S_T S_T g p T.base.value T.base.data ⟨0⟩ none H true with
            | .none => dbg_trace "Lambda returned none; this should probably not be happening; test semantics will be off."; default
            | .some x => x
        pure (σ_P, g', A, z)
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        let (_, σ_P, g',  A, z, _) ←
          Θ debugMode fuel T.blobVersionedHashes createdAccounts σ₀ AStar S_T S_T t (toExecute σ₀ t) g p T.base.value T.base.value T.base.data 0 H true
              --  dbg_trace "Θ gave back σ_P: {repr σ_P}"
        pure (σ_P, g', A, z)
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance S_T (gStar * p)
  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != ⟨0⟩ then
      σStar.increaseBalance H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ' -- (88)
  .ok (σ', A, z)
end EVM

end EvmYul
