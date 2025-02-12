import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.Account
import EvmYul.State.Block

import EvmYul.Maps.AccountMap

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Υᵍ`
-/
structure State where
  accountMap    : AccountMap
  σ₀            : AccountMap
  totalGasUsedInBlock  : ℕ
  substate      : Substate
  executionEnv  : ExecutionEnv
  blockHashes        : Array UInt256
  genesisBlockHeader : BlockHeader

  -- TODO(Keccak Stuff + I guess this will be gone so no need to nuke the `Finmap` just now
  -- keccakMap     : Batteries.RBMap (List UInt256) UInt256 compare
  keccakRange   : List UInt256
  usedRange     : Batteries.RBSet UInt256 compare
  hashCollision : Bool

  createdAccounts : Batteries.RBSet AccountAddress compare
deriving BEq, Inhabited, Repr

end EvmYul
