import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.List.Defs

import EvmYul.Data.Stack
import EvmYul.Operations
import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.ExecutionEnv
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.SharedStateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.Semantics
import EvmYul.Wheels

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

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : Nat) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let instr ← arr.get? pc >>= EvmYul.EVM.parseInstr
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

#check List.getLast

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error EVM.Exception.InvalidStackSizeException

-- def callDataLoad (μ₀ : UInt256)(Id : ByteArray) : UInt256 :=
--   open Array in
--   let vs : Array UInt256 := (Array.range 32).map (λ v => EvmYul.UInt256.ofNat v + μ₀)
--   sorry

-- def keccak256 : EVM.State → Except EVM.Exception EVM.State := sorry

local instance : MonadLift Option (Except EVM.Exception) :=
  ⟨Option.option (.error .InvalidStackSizeException) .ok⟩

mutual

def step (fuel : ℕ) : EVM.Transformer :=
  match fuel with
    | 0 => .ok
    | .succ f =>
    λ (evmState : EVM.State) ↦ do
    let (instr, arg) ← fetchInstr evmState.toState.executionEnv evmState.pc
    -- @Andrei: Of course not all can be shared, so based on `instr` this might not be `EvmYul.step`.
    match instr with
      | .Push _ => do
        let some (arg, argWidth) := arg | .error EVM.Exception.InvalidStackSizeException
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth)
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
            let Λ := Lambda f evmState.accountMap evmState.toState.substate Iₐ Iₒ I.gasPrice μ₀ i (Iₑ + 1) ζ I.header
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
            let Λ := Lambda f evmState.accountMap evmState.toState.substate Iₐ Iₒ I.gasPrice μ₀ i (Iₑ + 1) ζ I.header
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
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (σ', g', A', z, o) ← do
          -- TODO - Refactor condition and possibly share with CREATE
          if μ₂ ≤ (evmState.accountMap.lookup evmState.executionEnv.codeOwner |>.option 0 Account.balance) ∧ evmState.executionEnv.depth < 1024 then
            let t : Address := Address.ofUInt256 μ₁ -- t ≡ μs[1] mod 2^160
            let A' := evmState.addAccessedAccount t |>.substate -- A' ≡ A except A'ₐ ≡ Aₐ ∪ {t}
            let tDirect := evmState.accountMap.lookup t |>.get!.code -- We use the code directly without an indirection a'la `codeMap[t]`.
            let i := evmState.toMachineState.lookupMemoryRange μ₃ μ₄ -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
            Θ (σ  := evmState)                        -- σ in  Θ(σ, ..)
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
          else .ok (evmState, μ₀, evmState.toState.substate, false, ByteArray.empty)
        let n : UInt256 := min μ₆ o.size -- n ≡ min({μs[6], ‖o‖}) -- TODO - Why is this using... set??? { } brackets ???
        -- TODO I am assuming here that μ' is μ with the updates mentioned in the CALL section. Check.

        -- TODO - Note to self. Check how updateMemory/copyMemory is implemented. By a cursory look, we play loose with UInt8 -> UInt256 (c.f. e.g. `calldatacopy`) and then the interplay with the WordSize parameter.
        let μ'ₘ := List.range (n - 1) |>.foldl (init := evmState.toMachineState)
                     λ μ addr ↦ μ.copyMemory o μ₅ μ₆ -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]

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
              returnData := μ'ₒ
              gasAvailable := μ'_g
              maxAddress := μ'ᵢ }

        let σ' : EVM.State := {
          σ' with toMachineState := μ'incomplete
        }.replaceStackAndIncrPC μ'ₛ

        .ok σ'
      | instr => EvmYul.step instr evmState

def multistep (fuel : ℕ) (evmState : State) : Except EVM.Exception (State × ByteArray) := do
  match fuel with
    | 0 => .ok (evmState, .empty)
    | .succ f =>
      let (instr, _) ← fetchInstr evmState.toState.executionEnv evmState.pc
      let evmState' ← step f evmState
      match instr with
        | .RETURN | .REVERT => .ok <| (evmState', evmState'.returnData)
        | .STOP | .SELFDESTRUCT => .ok (evmState', .empty)
        | _ => multistep f evmState'

def Lambda
  (fuel : ℕ)
  (σ : Finmap (λ _ : Address ↦ Account))
  (A : Substate)
  (s : Address) -- sender
  (o : Address) -- original transactor
  (p : UInt256) -- gas price
  (v : UInt256) -- endowment
  (i : ByteArray) -- the initialisation EVM code
  (e : UInt256) -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt
  (H : BlockHeader)
  :
  Option (Address × Finmap (λ _ : Address ↦ Account) × Substate × Bool × ByteArray)
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
    ⟨1, v + v', .empty, fromBytes' (KEC default).data.data, default⟩

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
    , perm      := sorry -- TODO(Andrei)
    }
  let defState : EVM.State := default
  let freshEvmState : EVM.State :=
    { defState with
        accountMap := σStar
        executionEnv := exEnv
        substate := AStar
    }
  match multistep f freshEvmState with
    | .error _ => .none
    | .ok (evmState', returnedData) =>
      let F₀ : Bool :=
        match σ.lookup a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ 0
          | .none => false
      let σStarStar := evmState'.accountMap
      let F : Bool :=
        F₀ ∨ σStarStar ≠ ∅ ∨ returnedData.size > 24576
          ∨ returnedData = ByteArray.mk ⟨0xef :: returnedData.data.toList.tail⟩
      let fail := F ∨ σStarStar = ∅
      let σ' :=
        if fail then σ
          else if evmState'.dead a then (σStarStar.extract a).2
            else σStarStar.insert a {newAccount with code := returnedData}
      let A' := if fail then AStar else evmState'.substate
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
This invokes precompiled contracts based on the hash of the code.
Of course, we store the code directly.

TODO - Link to precompiles, investigate the return value.
Should this return the sender somehow ::thinking::?
-/
def Ξ (σ₁ : EVM.State) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
      EVM.State × UInt256 × Substate × ByteArray := sorry -- TODO - Wiat for this to exist.

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
-/
def Θ (σ  : EVM.State)
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
      (w  : Bool) : Except EVM.Exception (EVM.State × UInt256 × Substate × Bool × ByteArray) := do
  -- Equation (117)
  let σ₁sender ←
    if !σ.accountExists s && v == 0
    then throw .SenderMustExist -- TODO - YP explains the semantics of undefined receiver; what about sender? Cf. between (115) and (116).
    else σ.accountMap.lookup s |>.get!.subBalance v |>.elim (.error .Underflow) .ok -- Equation (118) TODO - What do we do on underflow?
  
  -- Equation (120)
  let σ₁receiver ←
    if !σ.accountExists s && v != 0
    then default else
    if !σ.accountExists s && v == 0
    then throw .ReceiverMustExistWithNonZeroValue else -- TODO - It seems that we must only initialise the account if v != 0. Otherwise the same question as with the non-existant sender.
    σ.accountMap.lookup r |>.get!.addBalance v |>.elim (.error .Overflow) .ok -- Equation (121) TODO - What do we do on overflow?

  -- (117) and (120) is `let σ₁ ← σ.transferBalance s r v` with some account updates.
  let σ₁ := σ.updateAccount s σ₁sender |>.updateAccount r σ₁receiver
  
  -- Equation (126)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (σ'', g'', A'', out) := Ξ σ₁ g A σ.toState.executionEnv
  
  -- Equation (122)
  let σ' := if σ''.isEmpty then σ else σ''

  -- Equation (123)
  let g' := if σ''.isEmpty && out.isEmpty then 0 else g''

  -- Equation (124)
  let A' := if σ''.isEmpty then A else A''

  -- Equation (125)
  let z := if σ''.isEmpty then false else true

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

  -- TODO - Not sure if I should be set here, or somehow pre-set for Xi.
  .ok ({ σ' with toState.executionEnv := I }, g', A', z, out)

end
-- open EvmYul.UInt256
-- def step : EvmYul.EVM.State → Except EVM.Exception EvmYul.EVM.State
-- | evmState@⟨sState@⟨state, mState⟩, pc, stack⟩ => do
--   match fetchInstr sState.toState.executionEnv pc with
--   | .error ex => .error ex
--   | .ok (i, pushArg?) =>
--     match i with
--     | .StopArith .STOP => .ok evmState
--     | .StopArith .ADD  => execBinOp UInt256.add evmState
--     | .StopArith .MUL => execBinOp UInt256.mul evmState
--     | .StopArith .SUB => execBinOp UInt256.sub evmState
--     | .StopArith .DIV => execBinOp UInt256.div evmState
--     | .StopArith .SDIV => execBinOp UInt256.sdiv evmState
--     | .StopArith .MOD => execBinOp UInt256.mod evmState
--     | .StopArith .SMOD => execBinOp UInt256.smod evmState
--     | .StopArith .ADDMOD => execTriOp addMod evmState
--     | .StopArith .MULMOD => execTriOp mulMod evmState
--     | .StopArith .EXP => execBinOp exp evmState
--     | .CompBit .LT => execBinOp lt evmState
--     | .CompBit .GT => execBinOp gt evmState
--     | .CompBit .SLT => execBinOp slt evmState
--     | .CompBit .SGT => execBinOp sgt evmState
--     | .CompBit .EQ => execBinOp eq evmState
--     | .CompBit .ISZERO => execUnOp isZero evmState
--     | .CompBit .AND => execBinOp UInt256.land evmState
--     | .CompBit .OR => execBinOp UInt256.lor evmState
--     | .CompBit .XOR => execBinOp UInt256.xor evmState
--     | .CompBit .NOT => execUnOp UInt256.lnot evmState
--     | .CompBit .BYTE => execBinOp UInt256.byteAt evmState
--     | .CompBit .SHL => execBinOp UInt256.shiftLeft evmState
--     | .CompBit .SHR => execBinOp UInt256.shiftRight evmState
--     | .CompBit .SAR => execBinOp UInt256.sar evmState
--     | .Keccak .KECCAK256 => sorry
--     | .StopArith .SIGNEXTEND =>
--         execBinOp
--           UInt256.signextend
--           -- (λ μ₀ μ₁ =>
--           --                  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
--           --                  let t  : Fin 256 := (256 - 8 * (μ₀ - 1)).1
--           --                  let v₂ : BitVec 256 := BitVec.ofFn λ i =>
--           --                    if i <= t then BitVec.getLsb v₁ t else BitVec.getLsb v₁ i
--           --                  UInt256.ofNat (BitVec.toNat v₂))
--           evmState
--     | .Env .ADDRESS => .ok <| evmState.replaceStackAndIncrPC (stack.push sState.toState.executionEnv.codeOwner)
--     | .Env .BALANCE =>
--       match Stack.pop stack with
--       | some ⟨ s , μ₀ ⟩ =>
--         let (state', a') := EvmYul.State.balance evmState.toSharedState.toState μ₀
--         let evmState' := {evmState with toSharedState.toState := state'}
--         -- let addr : _root_.Address := Fin.ofNat (Nat.mod μ₀.1 (2 ^ 160))
--         -- let σ₁ : EvmYul.EVMState := EvmYul.EVMState.addAccessedAccount addr σ
--         -- match Finmap.lookup addr σ.account_map with
--         -- | some v => inr (σ₁ , pushAndIncrPC v.balance s μ)
--         -- | _      => inr (σ₁ , pushAndIncrPC 0 s μ)
--         .ok <| evmState'.replaceStackAndIncrPC (s.push a')
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .ORIGIN => .ok <| evmState.replaceStackAndIncrPC (stack.push sState.toState.executionEnv.sender)
--     | .Env .CALLER => .ok <| evmState.replaceStackAndIncrPC (stack.push sState.toState.executionEnv.source)
--     | .Env .CALLVALUE => .ok <| evmState.replaceStackAndIncrPC (stack.push sState.toState.executionEnv.weiValue)
--     | .Env .CALLDATALOAD =>
--       match Stack.pop stack with
--       | some ⟨ _ , μ₀ ⟩ =>
--         let v : UInt256 := EvmYul.State.calldataload evmState.toSharedState.toState μ₀
--         .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .CALLDATASIZE =>
--       let v : UInt256 := UInt256.ofNat sState.toState.executionEnv.inputData.size
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Env .CALLDATACOPY =>
--       match Stack.pop3 stack with
--       | some ⟨ s , μ₀ , μ₁ , μ₂ ⟩ =>
--         -- TODO: doublecheck calldatacopy
--         let sState' := evmState.calldatacopy μ₀ μ₁ μ₂
--         let evmState' := { evmState with toSharedState := sState'}
--         -- maxAddress handled by updateMemory
--         -- let maxAddress' := M evmState'.maxAddress μ₀ μ₂
--         -- let evmState'' := { evmState' with maxAddress := maxAddress' }
--         .ok evmState'
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .CODESIZE => .ok <| evmState.replaceStackAndIncrPC (stack.push sState.toState.executionEnv.code.size)
--     | .Env .CODECOPY =>
--       match Stack.pop3 stack with
--       | some ⟨ s , μ₀ , μ₁ , μ₂ ⟩ =>
--         -- TODO: doublecheck codecopy
--         let sState' := sState.codeCopy μ₀ μ₁ μ₂
--         let evmState' := { evmState with toSharedState := sState'}
--         -- maxAddress handled by updateMemory?
--         -- let maxAddress' := M evmState'.maxAddress μ₀ μ₂
--         -- let evmState'' := { evmState' with maxAddress := maxAddress' }
--         .ok <| evmState'
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .GASPRICE =>
--       let v : UInt256 := UInt256.ofNat sState.toState.executionEnv.gasPrice
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Env .EXTCODESIZE =>
--       match Stack.pop stack with
--       | some ⟨ s , μ₀ ⟩ =>
--         let addr : Address := Fin.ofNat (Nat.mod μ₀.1 (2 ^ 160))
--         let state' : EvmYul.State := EvmYul.State.addAccessedAccount sState.toState addr
--         let evmState' := {evmState with toSharedState.toState := state'}
--         match Finmap.lookup addr evmState'.accountMap with
--         | some act => .ok <| evmState'.replaceStackAndIncrPC (stack.push act.code.size)
--         | _ => .ok <| evmState'.replaceStackAndIncrPC (stack.push 0)
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .EXTCODECOPY =>
--       match Stack.pop4 stack with
--       | some ⟨s, μ₀, μ₁, μ₂, μ₃⟩ =>
--         let addr : Address := Fin.ofNat (Nat.mod μ₀.1 (2 ^ 160))
--         let sState' := sState.extCodeCopy addr μ₁ μ₂ μ₃
--         let evmState' := {evmState with toSharedState := sState'}
--         -- maxAddress handled by updateMemory?
--         -- let maxAddress' := M mState.maxAddress μ₁ μ₃
--         -- let evmState'' := {evmState' with maxAddress := maxAddress'}
--         let state' : EvmYul.State := EvmYul.State.addAccessedAccount sState.toState addr
--         let evmState'' := {evmState' with toState := state'}
--         .ok evmState''
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .RETURNDATASIZE =>
--       let v := mState.returndatasize
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Env .RETURNDATACOPY =>
--       match Stack.pop3 stack with
--       | some ⟨ s , μ₀ , μ₁ , μ₂ ⟩ =>
--         let some mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂ | .error EVM.Exception.OutOfBounds
--         .ok <| {evmState with toMachineState := mState'}
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Env .EXTCODEHASH => sorry
--     | .Block .BLOCKHASH =>
--       match Stack.pop stack with
--       | some ⟨ s , μ₀ ⟩ =>
--         -- State.blockHash seems correct
--         let v : UInt256 := state.blockHash μ₀
--         .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Block .COINBASE =>
--       let v : UInt256 := sState.toState.executionEnv.header.beneficiary
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .TIMESTAMP =>
--       let v : UInt256 := UInt256.ofNat (sState.toState.executionEnv.header.timestamp)
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .NUMBER =>
--       let v : UInt256 := UInt256.ofNat (sState.toState.executionEnv.header.number)
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .DIFFICULTY =>
--       let v : UInt256 := UInt256.ofNat (sState.toState.executionEnv.header.difficulty)
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .GASLIMIT =>
--       let v : UInt256 := UInt256_returnedData.ofNat (sState.toState.executionEnv.header.gasLimit)
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .CHAINID =>
--       -- XXX The chainid β seem to be associated in transactions.
--       -- question: How transactions are denoted in the evm state?
--       let v : UInt256 := sState.toState.chainId
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .SELFBALANCE =>
--       let v : UInt256 := sState.toState.executionEnv.codeOwner
--       .ok <| evmState.replaceStackAndIncrPC (stack.push v)
--     | .Block .BASEFEE => sorry
--     | .Log _ => sorry -- How to model substate’s log series?
--     | .StackMemFlow .POP =>
--       match Stack.pop stack with
--       | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
--       | _ => .error EVM.Exception.InvalidStackSizeException
--     | .Push _ => do let some (arg, argWidth) := pushArg? | .error EVM.Exception.InvalidStackSizeException
--                     .ok <| evmState.replaceStackAndIncrPC (stack.push arg) (pcΔ := argWidth)
--     | _ => .ok evmState

end EVM

end EvmYul
