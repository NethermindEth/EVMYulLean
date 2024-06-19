import Mathlib.Data.Finmap
import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`. 
- `code` 
-/
structure Account :=
  nonce    : UInt256 
  balance  : UInt256
  code     : ByteArray
  codeHash : UInt256 -- TODO - Probably not needed.
  storage  : Storage
deriving DecidableEq, Inhabited

end EvmYul
