import EvmYul.Data.Stack

import EvmYul.State
import EvmYul.SharedState

namespace EvmYul

namespace EVM

/--
The EVM `State` (extends EvmYul.SharedState).
- `pc`         `pc`
- `stack`      `s`
- `execLength` - Length of execution.
-/
structure State extends EvmYul.SharedState .EVM where
  pc    : UInt256
  stack : Stack UInt256
  execLength : ℕ
  deriving Inhabited

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)

end EVM

end EvmYul
