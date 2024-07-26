import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.List.Defs

import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv

import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Semantics
import EvmYul.Wheels
import EvmYul.UInt256

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

def N (pc : Nat) (instr : Operation .EVM) := pc.succ + argOnNBytesOfInstr instr

abbrev YPState := Finmap (λ _ : Address ↦ Account)

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : Nat) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  -- dbg_trace s!"DECODING; arr: {arr} pc: {pc}"
  -- let wagh := arr.get? pc
  -- dbg_trace s!"wagh is: {wagh}"
  let instr ← arr.get? pc >>= EvmYul.EVM.parseInstr
  -- dbg_trace s!"AAAAA: {instr.pretty}"
  let argWidth := argOnNBytesOfInstr instr
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (EvmYul.uInt256OfByteArray (arr.extract pc.succ (pc.succ + argWidth)), argWidth)
  )

def fetchInstr (I : EvmYul.ExecutionEnv) (pc :  UInt256) :
               Except EVM.Exception (Operation .EVM × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .InvalidStackSizeException) Except.ok

partial def D_J (c : ByteArray) (i : ℕ) : List ℕ :=
  match c.get? i >>= EvmYul.EVM.parseInstr with
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
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < 32
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

def step (fuel : ℕ) : EVM.Transformer :=
  match fuel with
    | 0 => .ok
    | .succ f =>
    λ (evmState : EVM.State) ↦ do
    -- dbg_trace "FETCHING!"
    let (instr, arg) ← fetchInstr evmState.toState.executionEnv evmState.pc
    -- dbg_trace s!"step called with: {instr.pretty}"
    -- @Andrei: Of course not all can be shared, so based on `instr` this might not be `EvmYul.step`.
    match instr with
      | .Push _ => do
        let some (arg, argWidth) := arg | .error EVM.Exception.InvalidStackSizeException
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
      | .JUMP =>
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            match fetchInstr evmState.toState.executionEnv newPc with
              | .ok (.JUMPDEST, _) =>
                let evmState' := {evmState with pc := newPc}
                .ok <| evmState'.replaceStackAndIncrPC stack
              | _ => .error EVM.Exception.InvalidPC
          | _ => .error EVM.Exception.InvalidStackSizeException
      | .JUMPI =>
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ = 0 then evmState.pc + 1 else μ₀
            match fetchInstr evmState.toState.executionEnv newPc with
              | .ok (.JUMPDEST, _) =>
                let evmState' := {evmState with pc := newPc}
                .ok <| evmState'.replaceStackAndIncrPC stack
              | _ => .error EVM.Exception.InvalidPC
          | _ => .error EVM.Exception.InvalidStackSizeException
      | .PC =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
      | .JUMPDEST => .ok evmState

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
            let i : ByteArray := evmState.toMachineState.lookupMemoryRange μ₁ μ₂
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let Λ := Lambda f evmState.accountMap evmState.toState.substate Iₐ Iₒ I.gasPrice μ₀ i (Iₑ + 1) ζ I.header I.perm
            let (a, evmState', z, o) : (Address × EVM.State × Bool × ByteArray) :=
              if μ₀ ≤ (evmState.accountMap.lookup Iₐ |>.option 0 Account.balance) ∧ Iₑ < 1024 then
                match Λ with
                  | some (a, σ', A', z, o) =>
                    (a, {evmState with accountMap := σ', substate := A'}, z, o)
                  | none => (0, evmState, False, .empty)
              else
                (0, evmState, False, .empty)
            let x :=
              let balance := evmState.accountMap.lookup a |>.option 0 Account.balance
                if z = false ∨ Iₑ = 1024 ∨ μ₀ < balance then 0 else a
            let newReturnData : ByteArray := if z = false then .empty else o
            let μᵢ' := MachineState.M evmState.maxAddress μ₁ μ₂
            let evmState' :=
              {evmState' with
                toMachineState :=
                  {evmState.toMachineState with
                    returnData := newReturnData
                    maxAddress := μᵢ'
                  }
              }
            .ok <| evmState'.replaceStackAndIncrPC (evmState.stack.push x)
          | _ =>
          .error .InvalidStackSizeException
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            let i : ByteArray := evmState.toMachineState.lookupMemoryRange μ₁ μ₂
            let ζ := some ⟨⟨toBytesBigEndian μ₃.val⟩⟩
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let Λ := Lambda f evmState.accountMap evmState.toState.substate Iₐ Iₒ I.gasPrice μ₀ i (Iₑ + 1) ζ I.header I.perm
            let (a, evmState', z, o) : (Address × EVM.State × Bool × ByteArray) :=
              if μ₀ ≤ (evmState.accountMap.lookup Iₐ |>.option 0 Account.balance) ∧ Iₑ < 1024 then
                match Λ with
                  | some (a, σ', A', z, o) =>
                    (a, {evmState with accountMap := σ', substate := A'}, z, o)
                  | none => (0, evmState, False, .empty)
              else
                (0, evmState, False, .empty)
            let x :=
              let balance := evmState.accountMap.lookup a |>.option 0 Account.balance
                if z = false ∨ Iₑ = 1024 ∨ μ₀ < balance then 0 else a
            let newReturnData : ByteArray := if z = false then .empty else o
            let μᵢ' := MachineState.M evmState.maxAddress μ₁ μ₂
            let evmState' :=
              {evmState' with
                toMachineState :=
                  {evmState.toMachineState with
                    returnData := newReturnData
                    maxAddress := μᵢ'
                  }
              }
            .ok <| evmState'.replaceStackAndIncrPC (evmState.stack.push x)
          | _ =>
          .error .InvalidStackSizeException
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        -- dbg_trace "POPPING"
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        -- dbg_trace "POPPED OK; μ₁ : {μ₁}"
        -- dbg_trace s!"Pre call, we have: {Finmap.pretty evmState.accountMap}"
        let (σ', g', A', z, o) ← do
          -- TODO - Refactor condition and possibly share with CREATE
          if μ₂ ≤ (evmState.accountMap.lookup evmState.executionEnv.codeOwner |>.option 0 Account.balance) ∧ evmState.executionEnv.depth < 1024 then
            let t : Address := Address.ofUInt256 μ₁ -- t ≡ μs[1] mod 2^160
            let A' := evmState.addAccessedAccount t |>.substate -- A' ≡ A except A'ₐ ≡ Aₐ ∪ {t}
            -- TODO A minor... hack? Are we supposed to run into missing account here?
            let .some tDirect := evmState.accountMap.lookup t | throw (.ReceiverNotInAccounts t)
            let tDirect := tDirect.code -- We use the code directly without an indirection a'la `codeMap[t]`.
            let i := evmState.toMachineState.lookupMemoryRange μ₃ μ₄ -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
            Θ (fuel := f)                             -- TODO meh
              (σ  := evmState.accountMap)             -- σ in  Θ(σ, ..)
              (A  := A')                              -- A* in Θ(.., A*, ..)
              (s  := evmState.executionEnv.codeOwner) -- Iₐ in Θ(.., Iₐ, ..)
              (o  := evmState.executionEnv.sender)    -- Iₒ in Θ(.., Iₒ, ..)
              (r  := t)                               -- t in Θ(.., t, ..)
              (c  := tDirect)                         -- t in Θ(.., t, ..) except 'dereferenced'
              (g  := μ₀)                              -- TODO gas - CCALLGAS(σ, μ, A)
              (p  := evmState.executionEnv.gasPrice)  -- Iₚ in Θ(.., Iₚ, ..)
              (v  := μ₂)                              -- μₛ[2] in Θ(.., μₛ[2], ..)
              (v' := μ₂)                              -- μₛ[2] in Θ(.., μₛ[2], ..)
              (d  := i)                               -- i in Θ(.., i, ..)
              (e  := evmState.executionEnv.depth + 1) -- Iₑ + 1 in Θ(.., Iₑ + 1, ..)
              (w  := evmState.executionEnv.perm)      -- I_W in Θ(.., I_W)
          -- TODO gas - CCALLGAS(σ, μ, A)
          else .ok (evmState.toState.accountMap, μ₀, evmState.toState.substate, false, .some .empty) -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
        dbg_trace s!"THETA OK"
        let n : UInt256 := min μ₆ (o.elim 0 (UInt256.ofNat ∘ ByteArray.size)) -- n ≡ min({μs[6], ‖o‖}) -- TODO - Why is this using... set??? { } brackets ???
        -- TODO I am assuming here that μ' is μ with the updates mentioned in the CALL section. Check.

        -- TODO - Note to self. Check how updateMemory/copyMemory is implemented. By a cursory look, we play loose with UInt8 -> UInt256 (c.f. e.g. `calldatacopy`) and then the interplay with the WordSize parameter.
        -- TODO - Check what happens when `o = .none`.
        let μ'ₘ := evmState.toMachineState.copyMemory (o.getD .empty) μ₅ n -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]

        let μ'ₒ := o -- μ′o = o
        let μ'_g := g' -- TODO gas - μ′g ≡ μg − CCALLGAS(σ, μ, A) + g

        let codeExecutionFailed   : Bool := z -- TODO - This is likely wrong.
        let notEnoughFunds        : Bool := μ₂ > (evmState.accountMap.lookup evmState.executionEnv.codeOwner |>.elim 0 Account.balance) -- TODO - Unify condition with CREATE.
        let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
        let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then 0 else 1 -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let μ'ᵢ := MachineState.M (MachineState.M evmState.maxAddress μ₃ μ₄) μ₅ μ₆ -- μ′i ≡ M (M (μi, μs[3], μs[4]), μs[5], μs[6])

        -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
        let μ'incomplete : MachineState :=
          { μ'ₘ with
              returnData   := μ'ₒ.getD .empty -- TODO - Check stuff wrt. .none
              gasAvailable := μ'_g
              maxAddress   := μ'ᵢ }

        let σ' : EVM.State := { evmState with accountMap := σ', substate := A' }
        let σ' := {
          σ' with toMachineState := μ'incomplete
        }.replaceStackAndIncrPC μ'ₛ

        .ok σ'
      | instr => EvmYul.step instr evmState

def X (fuel : ℕ) (evmState : State) : Except EVM.Exception (State × Option ByteArray) := do
  -- dbg_trace s!"X?!"
  match fuel with
    | 0 => .ok (evmState, some .empty)
    | .succ f =>
      let I_b := evmState.toState.executionEnv.code
      let w :=
        match decode I_b evmState.pc with
          | some (w, _) => w
          | none => dbg_trace "GON STOP!"; .STOP
      -- dbg_trace s!"Executing: {w.pretty}"
      let W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
        w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4] ∨
        (w = .CALL ∧ s.get? 2 ≠ some 0)
      let Z : Bool :=
        δ w = none ∨
        evmState.stack.length < (δ w).getD 0 ∨
        (w = .JUMP ∧ notIn (evmState.stack.get? 0) (D_J I_b 0)) ∨
        (w = .JUMPI ∧ (evmState.stack.get? 0 ≠ some 0) ∧ notIn (evmState.stack.get? 1) (D_J I_b 0)) ∨
        (w = .RETURNDATACOPY ∧ evmState.stack.getD 1 0 + evmState.stack.getD 2 0 > evmState.returnData.size) ∨
        evmState.stack.length - (δ w).getD 0 - (α w).getD 0 > 1024 ∨
        ( (¬ evmState.executionEnv.perm) ∧ W w evmState.stack)

      let H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          some μ.returnData
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none

      if Z then
        .ok ({evmState with accountMap := ∅}, none)
      else
        if w = .REVERT then
          .ok ({evmState with accountMap := ∅}, some evmState.returnData)
        else
          let evmState' ← step f evmState
          match H evmState.toMachineState w with
            | none => X f evmState'
            | some o => .ok <| (evmState', some o)
 where
  belongs (o : Option ℕ) (l : List ℕ) : Bool :=
    match o with
      | none => false
      | some n => n ∈ l
  notIn (o : Option ℕ) (l : List ℕ) : Bool := not (belongs o l)

def Ξ (fuel : ℕ) (σ : YPState) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
  Except EVM.Exception (YPState × UInt256 × Substate × Option ByteArray)
:= do
  match fuel with
    | 0 => .ok (σ, g, A, some .empty) -- TODO - Gas model
    | .succ f =>
      let defState : EVM.State := default
      let freshEvmState : EVM.State :=
        { defState with
            accountMap := σ
            executionEnv := I
            substate := A
        }
      let (evmState', o) ← X f freshEvmState
      return (evmState'.accountMap, g, evmState'.substate, o) -- TODO - Gas model

def Lambda
  (fuel : ℕ)
  (σ : YPState)
  (A : Substate)
  (s : Address) -- sender
  (o : Address) -- original transactor
  (p : UInt256) -- gas price
  (v : UInt256) -- endowment
  (i : ByteArray) -- the initialisation EVM code
  (e : UInt256) -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt
  (H : BlockHeader)
  (w : Bool)
  :
  Option (Address × YPState × Substate × Bool × ByteArray)
:=
  match fuel with
    | 0 => .none
    | .succ f => do
  let n : UInt256 := (σ.lookup s |>.option 0 Account.nonce) - 1
  let lₐ ← L_A s n ζ i
  let a : Address :=
    (KEC lₐ).extract 96 265 |>.data.toList.reverse |> fromBytes' |> Fin.ofNat
  -- A*
  let AStar := A.addAccessedAccount a
  -- σ*
  let v' :=
    match σ.lookup a with
      | none => 0
      | some ac => ac.balance

  let newAccount : Account :=
    { nonce := 1
    , balance := v + v'
    , code := .empty
    , codeHash := fromBytes' (KEC default).data.data
    , storage := default
    , tstorage := default
    }

  let σStar :=
    match σ.lookup s with
      | none => σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount
  -- I
  let exEnv : ExecutionEnv :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , inputData := default
    , code      := i
    , gasPrice  := p
    , header    := H
    , depth     := e + 1
    , perm      := w
    }
  match Ξ f σStar 42 AStar exEnv with -- TODO - Gas model.
    | .error _ => .none
    | .ok (_, _, _, none) => .none
    | .ok (σStarStar, _, AStarStar, some returnedData) =>
      let F₀ : Bool :=
        match σ.lookup a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ 0
          | .none => false
      -- let σStarStar := evmState'.accountMap
      let F : Bool :=
        F₀ ∨ σStarStar ≠ ∅ ∨ returnedData.size > 24576
          ∨ returnedData = ⟨⟨(0xef :: returnedData.data.toList.tail)⟩⟩
      let fail := F ∨ σStarStar = ∅
      let σ' :=
        if fail then σ
          else if State.dead σStarStar a then (σStarStar.extract a).2
            else σStarStar.insert a {newAccount with code := returnedData}
      let A' := if fail then AStar else AStarStar
      let z := not fail
      .some (a, σ', A', z, returnedData)
 where
  L_A (s : Address) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  :=
    let s := (toBytesBigEndian s).toByteArray
    let n := (toBytesBigEndian n).toByteArray
    match ζ with
      | none =>
        match RLP <| .𝕃 [.𝔹 s, .𝔹 n] with
          | none => .none
          | some L_A => .some L_A
      | some ζ =>
        .some <| (toBytesBigEndian 255).toByteArray ++ s ++ ζ ++ KEC i

/--
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
def Θ (fuel : Nat)
      (σ  : YPState)
      (A  : Substate)
      (s  : Address)
      (o  : Address)
      (r  : Address)
      (c  : ByteArray)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Nat)
      (w  : Bool) : Except EVM.Exception (YPState × UInt256 × Substate × Bool × Option ByteArray) :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => do
  -- Equation (117)
  let σ₁sender ←
    if !s ∈ σ && v == 0
    then throw .SenderMustExist -- TODO - YP explains the semantics of undefined receiver; what about sender? Cf. between (115) and (116).
    else σ.lookup s |>.get!.subBalance v |>.elim (.error .Underflow) .ok -- Equation (118) TODO - What do we do on underflow?

  -- Equation (120)
  let σ₁receiver ←
    if !s ∈ σ && v != 0
    then default else
    if !s ∈ σ && v == 0
    then throw .ReceiverMustExistWithNonZeroValue else -- TODO - It seems that we must only initialise the account if v != 0. Otherwise the same question as with the non-existant sender.
    σ.lookup r |>.get!.addBalance v |>.elim (.error .Overflow) .ok -- Equation (121) TODO - What do we do on overflow?

  -- (117) and (120) is `let σ₁ ← σ.transferBalance s r v` with some account updates.
  let σ₁ := σ.insert s σ₁sender |>.insert r σ₁receiver

  let I : ExecutionEnv :=
    {
      codeOwner := r  -- Equation (127)
      sender    := o  -- Equation (128)
      source    := s  -- Equation (131)
      weiValue  := v' -- Equation (132)
      inputData := d  -- Equation (130)
      code      := c  -- Note that we don't use an address, but the actual code. Equation (136)-ish.
      gasPrice  := p  -- Equation (129)
      header    := default -- TODO - ?
      depth     := e  -- Equation (133)
      perm      := w  -- Equation (134)
    }


  -- Equation (126)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (σ'', g'', A'', out) ← Ξ fuel σ₁ g A I

  -- dbg_trace s!"Post Ξ we have: {Finmap.pretty σ''}"

  -- Equation (122)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (123)
  let g' := if σ'' == ∅ && out.isNone then 0 else g''

  -- Equation (124)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (125)
  let z := σ'' != ∅

  -- Equation (114)
  .ok (σ', g', A', z, out)

end

end EVM

end EvmYul
