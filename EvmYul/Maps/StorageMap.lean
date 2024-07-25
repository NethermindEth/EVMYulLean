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

import Mathlib.Data.Finmap
import Mathlib.Data.Multiset.Sort

import EvmYul.Wheels

namespace EvmYul

section RemoveLater

abbrev Storage : Type := Finmap (λ _ : UInt256 ↦ UInt256)

instance : LE ((_ : UInt256) × UInt256) where
  le lhs rhs := if lhs.1 = rhs.1 then lhs.2 ≤ rhs.2 else lhs.1 ≤ rhs.1

instance : IsTrans ((_ : UInt256) × UInt256) (· ≤ ·) where
  trans a b c h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    rcases c with ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
    unfold LE.le instLESigmaUInt256 at h₁ h₂ ⊢; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsAntisymm ((_ : UInt256) × UInt256) (· ≤ ·) where
  antisymm a b h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256 at h₁ h₂; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsTotal ((_ : UInt256) × UInt256) (· ≤ ·) where
  total a b := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256; simp
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : DecidableRel (α := (_ : UInt256) × UInt256) (· ≤ ·) :=
  λ a b ↦ by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256; simp
    aesop (config := {warnOnNonterminal := false}) <;> exact inferInstance

/--
It does _not_ matter how this is implemented at all, this is used _exclusively_ for convenience.
`Finmap`s are really clumsy.
-/
instance : LE EvmYul.Storage where
  le lhs rhs := let x := lhs.entries.sort (·≤·)
                let y := rhs.entries.sort (·≤·)
                Id.run do
                  let mut i := 0
                  let mut res := true
                  while true do
                    let xElem := x.get? i
                    let yElem := y.get? i
                    match xElem, yElem with
                      | .none, .none => break
                      | .some xElem, .some yElem => if xElem ≤ yElem then i := i + 1; continue else res := false; break
                      | .none, .some _ => res := true; break
                      | .some _, .none => res := false; break
                  return res

instance : DecidableRel (λ (lhs : EvmYul.Storage) rhs ↦ lhs ≤ rhs) :=
  λ lhs rhs ↦ by
    unfold LE.le instLEStorage
    simp
    exact inferInstance            

end RemoveLater

end EvmYul
