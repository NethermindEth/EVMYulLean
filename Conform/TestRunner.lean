import EvmYul.EVM.State
import EvmYul.EVM.Semantics
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
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        codeHash := 0 -- TODO - We can of course compute this but we probably do not need this.
        storage  := acc.storage.toFinmap
      }  
    { s with toState := s.setAccount addr account }

def Test.toTests (self : Test) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → EVM.State := Pre.toEVMState

def run : EVM.Transformer := EVM.step 5000 -- TODO - Replace with Xi or some such.

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

partial def runUntilStop : EVM.Transformer := λ s ↦
  match EvmYul.Conform.run s with
    | .error (.StopInvoked s) => pure s
    | .error e => .error e
    | .ok s => runUntilStop s

private def compareWithEVMdefaults (s₁ s₂ : EvmYul.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if 0 ∈ s then s else s.insert 0 0

private def somewhatShoddyAccEq (acc₁ acc₂ : Account) : Bool := acc₁ == acc₂

/--
TODO - Of course fix this later on. Potentially in some `Except Err` monad to report
precisely on why this failed.
-/
private def somewhatShoddyStateEq (s₁ s₂ : EVM.State) : Bool :=
  s₁.accountMap == s₂.accountMap

/--
TODO - This MUST use the transaction to initialise the `ExecutionEnv` of the `s`... somehow :).

This is marked `deprecated` to emit an error to make it clear that the implementation is placeholder.
-/
@[deprecated]
def executeTransaction (transaction : Transaction) (s : EVM.State) : Except EVM.Exception EVM.State :=
  runUntilStop s

/--
This assumes that the `transactions` are ordered.
-/
def preImpliesPost (pre : Pre) (post : Post) (transactions : Transactions) : Except EVM.Exception Bool :=
  somewhatShoddyStateEq post.toEVMState <$>
    transactions.foldlM (flip executeTransaction) pre.toEVMState

local instance : MonadLift (Except EVM.Exception) (Except Conform.Exception) := ⟨Except.mapError .EVMError⟩

def processTest (entry : TestEntry) : Except Exception TestResult := do
  -- From the tests eyeballed, there is a single block in 'blocks', so currently we assume this.
  let transactions := entry.blocks[0]!.transactions
  pure <| TestResult.ofBool (← preImpliesPost entry.pre entry.postState transactions)

local instance : MonadLift (Except String) (Except Conform.Exception) := ⟨Except.mapError .CannotParse⟩

def processTestsOfFile (file : System.FilePath) : ExceptT Exception IO (Lean.RBMap String TestResult compare) := do
  let file ← Lean.Json.fromFile file
  let test ← Lean.FromJson.fromJson? (α := Test) file
  test.toTests.foldlM (init := ∅) λ acc (testname, test) ↦
    processTest test >>= pure ∘ acc.insert testname

end Conform

end EvmYul
