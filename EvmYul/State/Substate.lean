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

structure LogEntry where
  address : AccountAddress
  topics  : Array UInt256
  data    : ByteArray
deriving BEq, Inhabited, Repr

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
  logSeries           : Array LogEntry
  deriving BEq, Inhabited, Repr

/--
  (63) `A0 ≡ (∅, (), ∅, 0, π, ∅)`
-/
def A0 : Substate := { (default : Substate) with accessedAccounts := π }

-- See the Bloom filter function M
def bloomFilter (a : Array ByteArray) : ByteArray  :=
  let zeroes : ByteArray := ByteArray.zeroes 256
  a.foldl set3Bits zeroes
 where
  setBit (bytes256 : ByteArray) (bitIndex : ℕ) : ByteArray :=
    let byteIndex := 255 - bitIndex / 8
    let mask : UInt8 := .ofNat <| 1 <<< (bitIndex % 8)
    let newByte := bytes256[byteIndex]! ||| mask
    bytes256.set! byteIndex newByte
  bitIndices (x : ByteArray) : List ℕ :=
    let kec := KEC x
    let lowOrder11Bits := λ b ↦ b &&& (1<<<11 - 1)
    [ kec.readWithPadding 0 2
    , kec.readWithPadding 2 2
    , kec.readWithPadding 4 2
    ].map (lowOrder11Bits ∘ fromByteArrayBigEndian)
  set3Bits acc b := bitIndices b |>.foldl setBit acc

def Substate.joinLogs (substate : Substate) : Array ByteArray :=
  Array.join <|
    substate.logSeries.map
      λ ⟨a, as, _⟩ ↦ (as.map UInt256.toByteArray).push a.toByteArray

end EvmYul
