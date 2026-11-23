/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Std.TreeMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Std.TreeMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Std.TreeMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Std.Data.TreeMap

import EvmYul.Wheels

namespace EvmYul

section RemoveLater

abbrev ByteMap := Std.TreeMap UInt256 UInt8 compare

end RemoveLater

end EvmYul
