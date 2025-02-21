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
  blocks        : ProcessedBlocks
  genesisBlockHeader : BlockHeader
  createdAccounts : Batteries.RBSet AccountAddress compare
deriving BEq, Inhabited, Repr

def State.blockHashes (self : State) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end EvmYul
