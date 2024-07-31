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
import Mathlib.Data.Multiset.Sort

import EvmYul.Wheels

namespace EvmYul

section RemoveLater

open Batteries (RBMap)

abbrev Storage : Type := RBMap UInt256 UInt256 compare

/--
It does _not_ matter how this is implemented at all, this is used _exclusively_ for convenience.
-/
instance : LT EvmYul.Storage where
  lt lhs rhs := let x := lhs.keysArray.zip lhs.valuesArray |>.qsort pairOrd
                let y := rhs.keysArray.zip rhs.valuesArray |>.qsort pairOrd
                Id.run do
                  let mut i := 0
                  let mut res := false
                  while true do
                    let xElem := x.get? i
                    let yElem := y.get? i
                    match xElem, yElem with
                      | .none, .none => break
                      | .some xElem, .some yElem =>
                          if pairOrd xElem yElem
                          then res := true; break
                          else if xElem != yElem
                               then break
                               else i := i + 1; continue
                      | .none, .some _ => res := true; break
                      | .some _, .none => res := false; break
                  return res
  where pairOrd (a b : UInt256 × UInt256) : Bool := -- TODO - surely there is some lex utility somewhere :)
    if a.1 = b.1 then a.2 < b.2 else a.1 < b.1

instance : DecidableRel (λ (a : EvmYul.Storage) b ↦ a < b) :=
  λ lhs rhs ↦ by
    unfold LT.lt instLTStorage
    simp
    exact inferInstance    

end RemoveLater

end EvmYul
