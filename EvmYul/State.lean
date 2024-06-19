import Mathlib.Data.Finmap
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
  accountMap    : Finmap (λ _ : Address ↦ Account)
  remainingGas  : ℕ
  substate      : Substate
  executionEnv  : ExecutionEnv

  -- Instead of keeping a map from `parentHash` to `Block`, we instead store the blocks we need.
  blocks        : List Block

  -- TODO(Keccak Stuff)
  keccakMap     : Finmap (λ _ : List UInt256 ↦ UInt256)
  keccakRange   : List UInt256
  usedRange     : Finset UInt256
  hashCollision : Bool
deriving DecidableEq, Inhabited

end EvmYul
