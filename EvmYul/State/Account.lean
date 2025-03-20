import EvmYul.Maps.StorageMap
import EvmYul.SpongeHash.Keccak256

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
  Precompiled contract addresses.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`
-/
def π : Batteries.RBSet AccountAddress compare :=
  Batteries.RBSet.ofList ((List.range 11).tail.map Fin.ofNat) compare

inductive ToExecute where | Code (code : ByteArray) | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : ByteArray
deriving BEq, Inhabited, Repr

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account extends PersistentAccountState where
  tstorage : Storage
deriving BEq, Inhabited, Repr

def PersistentAccountState.codeHash (self : PersistentAccountState) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

def Account.codeHash (self : Account) : UInt256 :=
  self.toPersistentAccountState.codeHash

end EvmYul
