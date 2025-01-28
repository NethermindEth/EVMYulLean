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
import EvmYul.State.TrieRoot
import EvmYul.SpongeHash.Keccak256

namespace EvmYul

section RemoveLater

abbrev Storage : Type := Batteries.RBMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def Storage.toEvmYulStorage (self : Storage) : EvmYul.Storage :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def toBlobs (pair : UInt256 × UInt256) : Option (String × String) := do
  -- dbg_trace "serialing storage item"
  let kec := KEC pair.1.toByteArray
  let rlp ← RLP (.𝔹 (BE pair.2.toNat))
  -- dbg_trace "done serialing storage item"
  pure (EvmYul.toHex kec, EvmYul.toHex rlp)

def computeTrieRoot (storage : Storage) : Option ByteArray :=
  match Array.mapM toBlobs storage.1.toArray with
    | none => .none
    | some pairs => (ByteArray.ofBlob (blobComputeTrieRoot pairs)).toOption

end RemoveLater

end EvmYul
