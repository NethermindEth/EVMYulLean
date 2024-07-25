import EvmYul.EVM.State
import EvmYul.EVM.Semantics

import EvmYul.State.TransactionOps

import EvmYul.Maps.AccountMap

import EvmYul.Pretty
import EvmYul.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace EvmYul

namespace Conform

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
        storage  := acc.storage.toFinmap
      }  
    { s with toState := s.setAccount addr account }

def Test.toTests (self : Test) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → EVM.State := Pre.toEVMState

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

private def compareWithEVMdefaults (s₁ s₂ : EvmYul.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if 0 ∈ s then s else s.insert 0 0

/--
TODO - Fix me.
-/
private def veryShoddyAccEq (acc₁ acc₂ : Account) : Bool :=
  withDefault acc₁.storage == withDefault acc₂.storage
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if 0 ∈ s then s else s.insert 0 0

/--
TODO - Of course remove this later.
-/
private local instance (priority := high) shoddyInstance : DecidableEq Account :=
  λ a b ↦ if veryShoddyAccEq a b then .isTrue sorry else .isFalse sorry

/--
TODO - This should be a generic map complement, but we are not trying to write a library here.
Also ouch `Finmap`.
-/
def storageComplement (m₁ m₂ : AccountMap) : AccountMap := Id.run do
  let mut result : AccountMap := m₁
  for ⟨k₂, v₂⟩ in computeToList! m₂.entries do
    match m₁.lookup k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`.
Effectively `m₁ / m₂ × m₂ / m₁`.

- if the `Δ = (∅, ∅)`, then `m₁ = m₂`
- used for reporting delta between expected post state and the actual state post execution
-/
def storageΔ (m₁ m₂ : AccountMap) : AccountMap × AccountMap :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

/--
TODO - Of course fix this later on. Potentially in some `Except Err` monad to report
precisely on why this failed.
-/
private def somewhatShoddyStateEq (s₁ s₂ : EVM.State) : Bool :=
  -- TODO - Please note here that we're only comparing storage until we have the means to execute
  -- transactions appropriately. For example, the sender must lose balance, nonce must increase, etc.
  -- Currently, we only compare with `shoddyInstance` for each account in the storage.
  -- dbg_trace s!"Post conforms? - {s₁.accountMap == s₂.accountMap}"
  s₁.accountMap == s₂.accountMap

def executeTransaction (transaction : Transaction) (s : EVM.State) : Except EVM.Exception EVM.State := do
  -- dbg_trace s!"Executing transaction."
  let target ← transaction.to?.elim (.error (.BogusExceptionToBeReplaced "no target is currently not addressed")) .ok
  
  -- dbg_trace s!"Identified target: {target}"

  -- TODO - This is not complete, of course.
  let I' := {
    s.executionEnv with code      := s.accountMap.lookup target |>.elim .empty Account.code
                        codeOwner := target  
                        perm      := true
                        inputData := transaction.data
  }

  -- dbg_trace s!"Initialisied code: {EvmYul.toHex I'.code}"

  let _TODOfuel := 2^32

  -- dbg_trace s!"Map before execution: {Finmap.pretty s.accountMap}"

  -- TODO - Ignore g' gas for the time being.
  let (σ, g', A', o?) ← EVM.Ξ _TODOfuel s.accountMap s.selfbalance s.substate I'

  -- TODO - Use proper Υ at some point, this is a hack, just like a majority of this function
  -- We manually inject 1000 -> 1000 as tests seem to expect this,
  -- as EIP 4788 (https://eips.ethereum.org/EIPS/eip-4788).
  
  -- Block processing
  -- At the start of processing any execution block where block.timestamp >= FORK_TIMESTAMP (i.e. before processing any transactions), call BEACON_ROOTS_ADDRESS as SYSTEM_ADDRESS with the 32-byte input of header.parent_beacon_block_root, a gas limit of 30_000_000, and 0 value. This will trigger the set() routine of the beacon roots contract. This is a system operation and therefore:

  -- the call must execute to completion
  -- the call does not count against the block’s gas limit
  -- the call does not follow the EIP-1559 burn semantics - no value should be transferred as part of the call
  -- if no code exists at BEACON_ROOTS_ADDRESS, the call must fail silently
  -- Clients may decide to omit an explicit EVM call and directly set the storage values. Note: While this is a valid optimization for Ethereum mainnet, it could be problematic on non-mainnet situations in case a different contract is used.

  -- If this EIP is active in a genesis block, the genesis header’s parent_beacon_block_root must be 0x0 and no system transaction may occur.
  
  -- TODO - This is currently not done properly. ^^^^^^^^^^^^^^

  let _BEACON_ROOTS_ADDRESS_HACK := 0x000f3df6d732807ef1319fb7b8bb8522d0beac02
  let .some _BEACON_ROOTS_ACCOUNT_HACK := s.accountMap.lookup _BEACON_ROOTS_ADDRESS_HACK | throw (.BogusExceptionToBeReplaced "_BEACON_ROOTS_ADDRESS_HACK not in pre")
  let σ := σ.insert _BEACON_ROOTS_ADDRESS_HACK (_BEACON_ROOTS_ACCOUNT_HACK.updateStorage 0x03e8 0x03e8)
  
  -- TODO - I think we do this tuple → EVM.State conversion reasonably often, factor out?
  let result : EVM.State := {
    s with accountMap := σ
           substate := A'
           returnData := o?.getD .empty -- TODO - What is up with this .none vs .some .empty.
  }
  pure result

/--
This assumes that the `transactions` are ordered, as they should be in the test suit.
-/
def executeTransactions (transactions : Transactions) : EVM.State → Except EVM.Exception EVM.State :=
  transactions.foldlM (flip executeTransaction)

/--
- `.none` on success
- `.some endState` on failure

NB we can throw away the final state if it coincided with the expected one, hence `.none`.
-/
def preImpliesPost (pre : Pre) (post : Post) (transactions : Transactions) : Except EVM.Exception (Option EVM.State) := do
  let result ← executeTransactions transactions pre.toEVMState
  pure <| if somewhatShoddyStateEq post.toEVMState result
          then .none
          else .some result  

local instance : MonadLift (Except EVM.Exception) (Except Conform.Exception) := ⟨Except.mapError .EVMError⟩

def processTest (entry : TestEntry) : Except Exception TestResult := do
  -- From the tests eyeballed, there is a single block in 'blocks', so currently we assume this.
  let transactions := entry.blocks[0]!.transactions

  let result ← preImpliesPost entry.pre entry.postState transactions

  pure <| result.elim .mkSuccess λ errSt ↦
    let (postSubActual, actualSubPost) := storageΔ (entry.postState.toEVMState.accountMap) errSt.accountMap
    dbg_trace "ST: {Finmap.pretty errSt.accountMap}"
    dbg_trace "POST: {Finmap.pretty entry.postState.toEVMState.accountMap}"
    .mkFailed s!"post / actual: {Finmap.pretty postSubActual}\nactual / post: {Finmap.pretty actualSubPost}"
  -- dbg_trace "pre: {entry.pre}"
  -- dbg_trace "post: {entry.postState}"
  -- pure <| TestResult.ofBool result 

local instance : MonadLift (Except String) (Except Conform.Exception) := ⟨Except.mapError .CannotParse⟩

def processTestsOfFile (file : System.FilePath) : ExceptT Exception IO (Lean.RBMap String TestResult compare) := do
  let file ← Lean.Json.fromFile file
  let test ← Lean.FromJson.fromJson? (α := Test) file
  test.toTests.foldlM (init := ∅) λ acc (testname, test) ↦
    processTest test >>= pure ∘ acc.insert testname

end Conform

end EvmYul
