import EvmYul.MachineState
import EvmYul.Yul.Wheels

namespace EvmYul

namespace Yul

/--
The partial Yul `MachineState` `μ`.
-/
structure MachineState extends EvmYul.MachineState :=
  varStore : VarStore
deriving DecidableEq, Inhabited

end Yul

end EvmYul
