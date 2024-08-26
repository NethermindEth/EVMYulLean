import EvmYul.EVM.State
import EvmYul.EVM.Semantics

import EvmYul.State.TransactionOps
import EvmYul.State.Withdrawal

import EvmYul.Maps.AccountMap

import EvmYul.Pretty
import EvmYul.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace EvmYul

namespace Conform

def VerySlowTests : Array String :=
  #[
    "sha3_d3g0v0_Cancun" -- ~6MB getting keccak256'd, estimated time on my PC: ~1 hour, best guess: unfoldr.go in keccak256.lean
    -- "sha3_d5g0v0_Cancun", -- best guess: `lookupMemoryRange'{'}{''}` are slow; I guess we will need an faster structure than Finmap
    -- "sha3_d6g0v0_Cancun" -- same problem as `sha3_d5g0v0_Cancun` I'm guessing
  ]

def GlobalBlacklist : Array String := VerySlowTests

def Pre.toEVMState (self : Pre) : EVM.State :=
  self.fold addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅ -- TODO - Look into transaciton storage.
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        codeHash := 0 -- TODO - We can of course compute this but we probably do not need this.
        storage  := acc.storage.toEvmYulStorage
      }
    { s with toState := s.setAccount addr account }

def Test.toTests (self : Test) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → EVM.State := Pre.toEVMState

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

private def compareWithEVMdefaults (s₁ s₂ : EvmYul.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if s.contains 0 then s else s.insert 0 0

/--
TODO - This should be a generic map complement, but we are not trying to write a library here.

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageComplement (m₁ m₂ : AccountMap) : AccountMap := Id.run do
  let mut result : AccountMap := m₁
  for ⟨k₂, v₂⟩ in m₂.toList do
    match m₁.find? k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`.
Effectively `m₁ / m₂ × m₂ / m₁`.

- if the `Δ = (∅, ∅)`, then `m₁ = m₂`
- used for reporting delta between expected post state and the actual state post execution

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageΔ (m₁ m₂ : AccountMap) : AccountMap × AccountMap :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

section

/--
This section exists for debugging / testing mostly. It's somewhat ad-hoc.
-/

notation "TODO" => default

private def almostBEqButNotQuiteEvmYulState (s₁ s₂ : EvmYul.State) : Except String Bool := do
  let s₁ := bashState s₁
  let s₂ := bashState s₂
  -- dbg_trace "expected:"
  -- s₁.accountMap.forM (λ addr acc ↦ dbg_trace (repr addr ++ ": ", repr acc.balance); .ok ())
  -- dbg_trace "got"
  -- s₂.accountMap.forM (λ addr acc ↦ dbg_trace (repr addr ++ ": ", repr acc.balance); .ok ())
  -- dbg_trace "\n"
  -- dbg_trace "expected:"
  -- dbg_trace repr s₁.accountMap
  -- dbg_trace "got"
  -- dbg_trace repr s₂.accountMap
  if s₁ == s₂ then .ok true else throw "state mismatch"
  -- if s₁.accountMap == s₂.accountMap then .ok true else throw "state mismatch: accountMap"
  -- if s₁.remainingGas == s₂.remainingGas then .ok true else throw "state mismatch: remainingGas"
  -- if s₁.substate == s₂.substate then .ok true else throw "state mismatch: substate"
  -- if s₁.executionEnv == s₂.executionEnv then .ok true else throw "state mismatch: executionEnv"
  -- if s₁.blocks == s₂.blocks then .ok true else throw "state mismatch: blocks"
  -- if s₁.keccakMap == s₂.keccakMap then .ok true else throw "state mismatch: keccakMap"
  -- if s₁.keccakRange == s₂.keccakRange then .ok true else throw "state mismatch: keccakRange"
  -- if s₁.usedRange == s₂.usedRange then .ok true else throw "state mismatch: usedRange"
  -- if s₁.hashCollision == s₂.hashCollision then .ok true else throw "state mismatch: hashCollision"
  -- if s₁.createdAccounts == s₂.createdAccounts then .ok true else throw "state mismatch: createdAccounts"
  where bashState (s : EvmYul.State) : EvmYul.State :=
    { s with
      accountMap := s.accountMap.map (λ (addr, acc) ↦ (addr, { acc with balance := TODO }))
      executionEnv.perm := TODO
      substate.accessedAccounts := TODO
      substate.accessedStorageKeys := TODO }

/--
NB it is ever so slightly more convenient to be in `Except String Bool` here rather than `Option String`.

This is morally `s₁ == s₂` except we get a convenient way to both tune what is being compared
as well as report fine grained errors.
-/
private def almostBEqButNotQuite (s₁ s₂ : EVM.State) : Except String Bool := do
  let miscEq := s₁.pc == s₂.pc && s₁.stack == s₂.stack
  if !miscEq then throw s!"pc / stack mismatch"

  discard <| almostBEqButNotQuiteEvmYulState s₁.toState s₂.toState

  let machineStEq := s₁.toMachineState == s₂.toMachineState
  if !machineStEq then throw s!"machine state mismatch"

  pure true -- Yes, we never return false, because we throw along the way. Yes, this is `Option`.

end

def executeTransaction (transaction : Transaction) (s : EVM.State) (header : BlockHeader) : Except EVM.Exception EVM.State := do
  let _TODOfuel := 2^13

  let (ypState, substate, z) ← EVM.Υ _TODOfuel s.accountMap header.chainId header.baseFeePerGas header transaction -- (dbgOverrideSender := transaction.base.dbgSender)

  -- as EIP 4788 (https://eips.ethereum.org/EIPS/eip-4788).

  -- TODO - I think we do this tuple → EVM.State conversion reasonably often, factor out?
  let result : EVM.State := {
    s with accountMap := ypState
           substate := substate
           executionEnv.perm := z -- TODO - that's probably not this :)
           -- returnData := TODO?
  }
  pure result

/--
This assumes that the `transactions` are ordered, as they should be in the test suit.
-/
def executeTransactions (blocks : Blocks) (s₀ : EVM.State) : Except EVM.Exception EVM.State := do
  blocks.foldlM processBlock s₀
  where processBlock (s : EVM.State) (block : BlockEntry) : Except EVM.Exception EVM.State := do
    -- We should not check the timestamp. Some tests have timestamp less than 1710338135 but still need EIP-4788
    -- let FORK_TIMESTAMP := 1710338135
    let _TODOfuel := 2^13
    let SYSTEM_ADDRESS := 0xfffffffffffffffffffffffffffffffffffffffe
    let BEACON_ROOTS_ADDRESS := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
    -- if no code exists at `BEACON_ROOTS_ADDRESS`, the call must fail silently
    let s ←
      match s.accountMap.find? BEACON_ROOTS_ADDRESS with
        | none => pure s
        | some roots =>
          let beaconRootsAddressCode := roots.code
          -- the call does not count against the block’s gas limit
          let (createdAccounts, σ, _, substate, _ /- can't fail-/, _) ←
            EVM.Θ
              _TODOfuel
              .empty
              s.accountMap
              default
              SYSTEM_ADDRESS
              SYSTEM_ADDRESS
              BEACON_ROOTS_ADDRESS
              beaconRootsAddressCode
              0 -- to be 30000000
              0xe8d4a51000
              0
              0
              block.blockHeader.parentBeaconBlockRoot
              0
              block.blockHeader
              true
          pure <|
            {s with
              createdAccounts := createdAccounts
              accountMap := σ
              substate := substate
            }
    let s ← block.transactions.foldlM
      (λ s trans ↦
        try
          executeTransaction trans s block.blockHeader
        catch e =>
          if !block.exception.isEmpty then
            dbg_trace s!"Expected exception: {block.exception}; got exception: {repr e} - we need to reconcile these as we debug tests. Currently, we mark the test as 'passed' as I assume this is the right kind of exception, but it doesn't need to be the case necessarily."
            throw <| EVM.Exception.ExpectedException block.exception
          else throw e
      )
      s
    let σ ←
      ( try
         applyWithdrawals
          s.accountMap
          block.blockHeader.withdrawalsRoot
          block.withdrawals
        catch e =>
          if !block.exception.isEmpty then
            dbg_trace s!"Expected exception: {block.exception}; got exception: {repr e} - we need to reconcile these as we debug tests. Currently, we mark the test as 'passed' as I assume this is the right kind of exception, but it doesn't need to be the case necessarily."
            throw <| EVM.Exception.ExpectedException block.exception
          else throw e
      )
    pure <| { s with accountMap := σ }
    -- pure s

/--
- `.none` on success
- `.some endState` on failure

NB we can throw away the final state if it coincided with the expected one, hence `.none`.
-/
def preImpliesPost (pre : Pre) (post : Post) (blocks : Blocks) : Except EVM.Exception (Option EVM.State) := do
  try
    let result ← executeTransactions blocks pre.toEVMState
    match almostBEqButNotQuite post.toEVMState result with
      | .error _ => pure (.some result) -- Feel free to inspect this error from `almostBEqButNotQuite`.
      | .ok _ => pure .none
  catch | .ExpectedException _ => pure .none -- An expected exception was thrown, which means the test is ok.
        | e                    => throw e

-- local instance : MonadLift (Except EVM.Exception) (Except Conform.Exception) := ⟨Except.mapError .EVMError⟩

-- vvvvvvvvvvvvvv DO NOT DELETE PLEASE vvvvvvvvvvvvvvvvvv
def DONOTDELETEMEFORNOW : AccountMap := Batteries.RBMap.ofList [(1, { dflt with storage := Batteries.RBMap.ofList [(44, 45), (46, 47)] compare }), (3, default)] compare
  where dflt : Account := default

instance (priority := high) : Repr AccountMap := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(EvmYul.toHex k.toByteArray) |>.takeRight 5}]\n"
      result := result ++ s!"balance: {v.balance}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩

def processTest (entry : TestEntry) (verbose : Bool := true) : TestResult :=
  let result := preImpliesPost entry.pre entry.postState entry.blocks
  match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => errorF <$> result

  where discardError : EVM.State → String := λ _ ↦ "ERROR."
        verboseError : EVM.State → String := λ s ↦
          let (postSubActual, actualSubPost) := storageΔ entry.postState.toEVMState.accountMap s.accountMap
          s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
        errorF := if verbose then verboseError else discardError

local instance : MonadLift (Except String) (Except Conform.Exception) := ⟨Except.mapError .CannotParse⟩

def processTestsOfFile (file : System.FilePath)
                       (whitelist : Array String := #[])
                       (blacklist : Array String := #[]) :
                       ExceptT Exception IO (Batteries.RBMap String TestResult compare) := do
  let file ← Lean.Json.fromFile file
  let test ← Lean.FromJson.fromJson? (α := Test) file
  -- dbg_trace s!"tests before guard: {test.toTests.map Prod.fst}"
  let tests := guardBlacklist ∘ guardWhitelist <| test.toTests
  -- dbg_trace s!"tests after guard: {tests.map Prod.fst}"
  tests.foldlM (init := ∅) λ acc (testname, test) ↦ pure <| acc.insert testname (processTest test)
    -- try
    --   processTest test >>= pure ∘
    --   -- TODO currently the soft errors are the ones I am personally unsure about :)
    -- catch
    --   | e => pure (acc.insert testname (.mkFailed s!"{repr e}"))
    -- -- catch | .EVMError e@(.ReceiverNotInAccounts _) => pure (acc.insert testname (.mkFailed s!"{repr e}"))
    -- --       | e => throw e -- hard error, stop executing the tests; malformed input, logic error, etc.
    -- --                      -- This should not happen but makes cause analysis easier if it does.
  where
    guardWhitelist (tests : List (String × TestEntry)) :=
      if whitelist.isEmpty then tests else tests.filter (λ (name, _) ↦ name ∈ whitelist)
    guardBlacklist (tests : List (String × TestEntry)) :=
      tests.filter (λ (name, _) ↦ name ∉ GlobalBlacklist ++ blacklist)

end Conform

end EvmYul
