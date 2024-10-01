/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import EvmYul.Wheels

namespace EvmYul

section RemoveLater

abbrev ByteMap := Batteries.RBMap UInt256 UInt8 compare

-- instance : LE ((_ : UInt256) × UInt8) where
--   le lhs rhs := if lhs.1 = rhs.1 then lhs.2 ≤ rhs.2 else lhs.1 ≤ rhs.1

-- /-
-- Please note that these are used exclusively for conveninece of printing and computing,
-- i.e. the sorries are safe.
-- -/

-- instance : IsTrans ((_ : UInt256) × UInt8) (· ≤ ·) := sorry

-- instance : IsAntisymm ((_ : UInt256) × UInt8) (· ≤ ·) := sorry

-- instance : IsTotal ((_ : UInt256) × UInt8) (· ≤ ·) := sorry

-- instance : DecidableRel (α := (_ : UInt256) × UInt8) (· ≤ ·) :=
--   λ lhs rhs ↦ by
--   unfold LE.le instLESigmaUInt256UInt8
--   exact inferInstance

end RemoveLater

end EvmYul
