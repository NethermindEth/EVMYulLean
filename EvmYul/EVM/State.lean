import EvmYul.Data.Stack

import EvmYul.State
import EvmYul.SharedState

namespace EvmYul

namespace EVM

/--
The EVM `State` (extends EvmYul.SharedState).
- `pc`         `pc`- The program counter.
- `stack`      `s`
-/
structure State extends EvmYul.SharedState :=
  pc    : UInt256
  stack : Stack UInt256
  -- TODO: temporary
  execLength : ℕ
  deriving Inhabited

inductive ExecutionResult (S : Type) :=
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)

end EVM

end EvmYul
