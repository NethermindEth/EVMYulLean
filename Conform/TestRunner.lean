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

/-
TODO - Remove these debugging instances.
-/

-- private local instance : ToString Account := ⟨λ acc ↦ s!"ACCOUNT: {Finmap.pretty acc.storage}"⟩

-- private local instance : LE EvmYul.Storage where
--   le lhs rhs := let x := lhs.entries.sort (·≤·)
--                 let y := rhs.entries.sort (·≤·)
--                 Id.run do
--                   let mut i := 0
--                   let mut res := true
--                   while true do
--                     let xElem := x.get? i
--                     let yElem := y.get? i
--                     match xElem, yElem with
--                       | .none, .none => break
--                       | .some xElem, .some yElem => if xElem ≤ yElem then i := i + 1; continue else res := false; break
--                       | .none, .some _ => res := true; break
--                       | .some _, .none => res := false; break
--                   return res

-- private local instance : LE Account where
--   le lhs rhs := lhs.storage ≤ rhs.storage

-- private local instance : LE ((_ : Address) × Account) where
--   le lhs rhs := if lhs.1 = rhs.1 then lhs.2 ≤ rhs.2 else lhs.1 ≤ rhs.1

-- /--
-- TODO - Doesn't matter for eyeballing. Remove later.
-- -/
-- private local instance : IsTrans ((_ : Address) × Account) fun x x_1 => x ≤ x_1 := sorry

-- private local instance : IsAntisymm ((_ : Address) × Account) fun x x_1 => x ≤ x_1 := sorry

-- private local instance : IsTotal ((_ : Address) × Account) fun x x_1 => x ≤ x_1 := sorry

-- private local instance : DecidableRel fun (x : Account) x_1 => x ≤ x_1 := by
--   unfold LE.le EvmYul.Conform.instLEAccount_conform
--   dsimp
--   unfold LE.le EvmYul.Conform.instLEStorage_conform
--   simp
--   intros a b
--   exact inferInstance

-- private local instance : DecidableRel fun x x_1 => (x : (_ : Address) × Account) ≤ x_1 :=
--   λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ↦ by 
--     dsimp; unfold LE.le EvmYul.Conform.instLESigmaAddressAccount_conform
--     exact inferInstance

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

  -- dbg_trace s!"Map after execution: {Finmap.pretty σ}"

  -- TODO - I think we do this tuple → EVM.State conversion reasonably often, factor out?
  let result : EVM.State := {
    s with accountMap := σ
           substate := A'
           returnData := o?.getD .empty -- TODO - What is up with this .none vs .some .empty.
  }
  pure result

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
  -- dbg_trace "pre: {entry.pre}"
  -- dbg_trace "post: {entry.postState}"
  pure <| TestResult.ofBool (← preImpliesPost entry.pre entry.postState transactions)

local instance : MonadLift (Except String) (Except Conform.Exception) := ⟨Except.mapError .CannotParse⟩

def processTestsOfFile (file : System.FilePath) : ExceptT Exception IO (Lean.RBMap String TestResult compare) := do
  let file ← Lean.Json.fromFile file
  let test ← Lean.FromJson.fromJson? (α := Test) file
  test.toTests.foldlM (init := ∅) λ acc (testname, test) ↦
    processTest test >>= pure ∘ acc.insert testname

end Conform

end EvmYul
