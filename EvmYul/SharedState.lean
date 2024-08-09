import EvmYul.State
import EvmYul.MachineState

namespace EvmYul

structure SharedState extends EvmYul.State, EvmYul.MachineState
  deriving BEq, Inhabited, Repr

end EvmYul
