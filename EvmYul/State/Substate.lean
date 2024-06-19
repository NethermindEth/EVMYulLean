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
  touchedAccounts      : Finset Account
  refundBalance        : UInt256
  accessedAccounts     : Finset Address
  accessedStorageKeys  : Finset (Address × UInt256)
  logSeries            : Array (Address × List UInt256 × ByteArray)
  deriving DecidableEq, Inhabited

end EvmYul
