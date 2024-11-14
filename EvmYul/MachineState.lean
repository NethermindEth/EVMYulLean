import FastMemset

import Batteries

import EvmYul.Maps.ByteMap
import EvmYul.UInt256
import Batteries.Data.HashMap
import EvmYul.MachineMemory

namespace EvmYul

open Batteries

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`   `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  gasAvailable        : UInt256
  activeWords         : UInt256
  activeWordsWritten  : UInt256
  memory              : Memory
  returnData          : ByteArray
  H_return            : ByteArray
  deriving Inhabited

-- inductive WordSize := | Standard | Single

-- def WordSize.toNat (this : WordSize) : ℕ :=
--   match this with
--     | WordSize.Standard => 32
--     | WordSize.Single   => 1

-- instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end EvmYul
