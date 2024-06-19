import Mathlib.Data.Finset.Basic

import EvmYul.State.BlockHeader
import EvmYul.State.Transaction

namespace EvmYul

/--
`Block`. `B<x>`. Section 4.3.
`blockHeader`  `H`
`transactions` `T`
`ommers`       `U` [deprecated]
-/
structure Block where
  blockHeader  : BlockHeader
  transactions : List Transaction
  ommers       : Finset BlockHeader := ∅
  deriving Inhabited, DecidableEq

attribute [deprecated] Block.ommers

end EvmYul
