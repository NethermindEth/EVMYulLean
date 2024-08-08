import Mathlib.Data.Finset.Basic

import EvmYul.State.BlockHeader
import EvmYul.State.Transaction

namespace EvmYul

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

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
  deriving Inhabited, BEq, Repr

attribute [deprecated] Block.ommers

end EvmYul
