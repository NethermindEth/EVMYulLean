import EvmYul.State
import EvmYul.MachineState

namespace EvmYul

structure SharedState (τ : OperationType) extends EvmYul.State τ, EvmYul.MachineState
  deriving Inhabited

end EvmYul
