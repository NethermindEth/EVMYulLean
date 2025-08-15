import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.Account
import EvmYul.State.Block
import EvmYul.State.Substate
import EvmYul.State.Transaction

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
structure State (τ : OperationType) where
  accountMap          : AccountMap τ
  σ₀                  : AccountMap .EVM
  totalGasUsedInBlock : ℕ
  transactionReceipts  : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv τ
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Batteries.RBSet AccountAddress compare
deriving Inhabited

def State.blockHashes {τ} (self : State τ) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end EvmYul
