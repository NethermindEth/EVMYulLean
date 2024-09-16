import Mathlib.Data.Finmap

import EvmYul.Wheels
import EvmYul.Yul.Wheels
import EvmYul.SharedState

namespace EvmYul

namespace Yul

/--
A jump in control flow containing a checkpoint of the state at jump-time.
- `Continue`: yul `continue` was encountered
- `Break`   : yul `break` was encountered
- `Leave`   : evm `return` was encountered
-/
inductive Jump where
  | Continue : EvmYul.SharedState → VarStore → Jump
  | Break    : EvmYul.SharedState → VarStore → Jump
  | Leave    : EvmYul.SharedState → VarStore → Jump

/--
The Yul `State`.
- `Ok state varstore` : The underlying `EvmYul.State` `state` along with `varstore`.
- `OutOfFuel`         : No state.
- `Checkpoint`        : Restore a previous state due to control flow.

The definition is ever so slightly off due to historical reasons.
-/
inductive State where
  | Ok         : EvmYul.SharedState → VarStore → State
  | OutOfFuel  : State
  | Checkpoint : Jump → State

instance : Inhabited State where
  default := .Ok default default

namespace State

def sharedState : State → EvmYul.SharedState
  | Ok sharedState _ => sharedState
  | _ => default

end State

end Yul

end EvmYul
