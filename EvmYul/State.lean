import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.Account
import EvmYul.State.Block

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `remainingGas` `g`
-/
structure State where
  accountMap    : Batteries.RBMap Address Account compare
  remainingGas  : ℕ
  substate      : Substate
  executionEnv  : ExecutionEnv

  -- Instead of keeping a map from `parentHash` to `Block`, we instead store the blocks we need.
  blocks        : List Block

  -- TODO(Keccak Stuff + I guess this will be gone so no need to nuke the `Finmap` just now
  keccakMap     : Batteries.RBMap (List UInt256) UInt256 compare
  keccakRange   : List UInt256
  usedRange     : Batteries.RBSet UInt256 compare
  hashCollision : Bool
deriving BEq, Inhabited, Repr

end EvmYul
