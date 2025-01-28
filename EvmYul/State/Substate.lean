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
def Substate.storageKeysCmp (sk₁ sk₂ : AccountAddress × UInt256) : Ordering :=
  lexOrd.compare sk₁ sk₂

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
  selfDestructSet     : Batteries.RBSet AccountAddress compare
  touchedAccounts     : Batteries.RBSet AccountAddress compare
  refundBalance       : UInt256
  accessedAccounts    : Batteries.RBSet AccountAddress compare
  accessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp
  logSeries           : Array (AccountAddress × List UInt256 × ByteArray)
  deriving BEq, Inhabited, Repr

/--
  (63) `A0 ≡ (∅, (), ∅, 0, π, ∅)`
-/
def A0 : Substate := { (default : Substate) with accessedAccounts := π }

end EvmYul
