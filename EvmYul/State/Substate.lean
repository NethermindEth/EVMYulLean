import Batteries.Data.RBMap
import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.Account

namespace EvmYul

/--
Not important for reasoning about Substate, this is currently done to get some nice performance properties
of the `Batteries.RBMap`.

TODO - to reason about the model, we will be better off with `Finset` or some such - 
without the requirement of ordering.

The current goal is to make sure that the model is executable and conformance-testable
before we make it easy to reason about.
-/
def Substate.accountCmp (acc₁ acc₂ : Account) : Ordering :=
  compareOfLessAndBEq acc₁.storage acc₂.storage

/--
Not important for reasoning about Substate, this is currently done to get some nice performance properties
of the `Batteries.RBMap`.

TODO - to reason about the model, we will be better off with `Finset` or some such - 
without the requirement of ordering.

The current goal is to make sure that the model is executable and conformance-testable
before we make it easy to reason about.
-/
def Substate.storageKeysCmp (sk₁ sk₂ : Address × UInt256) : Ordering :=
  have : DecidableRel (λ (x : Address × UInt256) y ↦ x < y) := by
    unfold LT.lt Preorder.toLT Prod.instPreorder
    simp
    exact inferInstance    
  compareOfLessAndBEq sk₁ sk₂ 

/--
The `Substate` `A`. Section 6.1.
- `selfDestructSet`    `Aₛ`
- `touchedAccounts`    `Aₜ`
- `refundBalance`      `Aᵣ`
- `accessedAccounts`   `Aₐ`
- `accessedStorageKey` `Aₖ`
- `logSeries`          `Aₗ`
-/
structure Substate :=
  selfDestructSet     : Batteries.RBSet Address compare
  touchedAccounts     : Batteries.RBSet Account Substate.accountCmp
  refundBalance       : UInt256
  accessedAccounts    : Batteries.RBSet Address compare
  accessedStorageKeys : Batteries.RBSet (Address × UInt256) Substate.storageKeysCmp
  logSeries           : Array (Address × List UInt256 × ByteArray)
  deriving BEq, Inhabited

end EvmYul
