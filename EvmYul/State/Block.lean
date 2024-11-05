import Mathlib.Data.Finset.Basic

import EvmYul.State.BlockHeader
import EvmYul.State.Transaction
import EvmYul.State.Withdrawal

namespace EvmYul

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

/--
`Block`. `B<x>`. Section 4.3.
`blockHeader`  `H`
`transactions` `T`
`ommers`       `U` [deprecated]
-/
structure Block where
  blockHeader  : BlockHeader
  rlp          : ByteArray
  transactions : Transactions
  withdrawals  : Withdrawals
  exception    : String
  -- An empty array which was previously reserved for ommer block headers,
  ommers       : Array BlockHeader := ∅
  -- blocknumber  : Nat
  deriving BEq, Inhabited, Repr

attribute [deprecated] Block.ommers

abbrev Blocks := Array Block

end EvmYul
