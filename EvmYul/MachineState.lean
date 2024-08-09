import EvmYul.Maps.ByteMap
import EvmYul.UInt256

namespace EvmYul

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `maxAddress`   `i` - # active words (modelled as the highest accessed address).
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  gasAvailable : UInt256
  maxAddress   : UInt256
  memory       : ByteArray
  returnData   : ByteArray
  deriving BEq, Inhabited, Repr

inductive WordSize := | Standard | Single

def WordSize.toNat (this : WordSize) : ℕ :=
  match this with
    | WordSize.Standard => 32
    | WordSize.Single   => 1

instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end EvmYul
