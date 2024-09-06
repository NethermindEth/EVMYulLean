import EvmYul.State
import EvmYul.MachineState

namespace EvmYul

structure SharedState extends EvmYul.State, EvmYul.MachineState
  deriving Inhabited

end EvmYul
