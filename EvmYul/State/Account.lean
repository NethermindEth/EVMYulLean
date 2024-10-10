import EvmYul.Maps.StorageMap
import EvmYul.SpongeHash.Keccak256

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9}`
-/
def π : Batteries.RBSet AccountAddress compare := Batteries.RBSet.ofList ((List.range 10).tail.map Fin.ofNat) compare

inductive ToExecute := | Code (code : ByteArray) | Precompiled (precompiled : AccountAddress)

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`

- `ostorage` holds `σ₀`, not a part of the YP
-/
structure Account :=
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  ostorage : Storage
  tstorage : Storage
  code     : ByteArray
deriving BEq, Inhabited, Repr

def Account.codeHash (self : Account) : UInt256 :=
  fromBytesBigEndian (KEC self.code).data.data

end EvmYul
