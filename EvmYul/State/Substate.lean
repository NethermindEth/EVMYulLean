import Mathlib.Data.Finset.Basic
import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.Account

namespace EvmYul

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
  selfDestructSet      : Finset Address
  touchedAccounts      : Finset Address
  refundBalance        : UInt256
  accessedAccounts     : Finset Address
  accessedStorageKeys  : Finset (Address × UInt256)
  logSeries            : Array (Address × List UInt256 × ByteArray)
  deriving DecidableEq, Inhabited

/--
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9}`
-/
def π : Finset Address := List.toFinset <| (List.range 10).tail.map Fin.ofNat

/--
  (63) `A0 ≡ (∅, (), ∅, 0, π, ∅)`
-/
def A0 : Substate := { (default : Substate) with accessedAccounts := π }

end EvmYul
