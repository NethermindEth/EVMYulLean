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

import EvmYul.Maps.StorageMap

import EvmYul.State.Account
import EvmYul.State.AccountOps

namespace EvmYul

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Batteries.RBMap AccountAddress α compare
abbrev AccountMap := AddrMap Account
abbrev PersistentAccountMap := AddrMap PersistentAccountState
def AccountMap.toPersistentAccountMap (a : AccountMap) : PersistentAccountMap :=
  a.mapVal (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance (σ : AccountMap) (addr : AccountAddress) (amount : UInt256)
  : AccountMap
:=
  match σ.find? addr with
    | none => σ.insert addr {(default : Account) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

def toExecute (σ : AccountMap) (t : AccountAddress) : ToExecute :=
  if /- t is a precompiled account -/ t ∈ π then
    ToExecute.Precompiled t
  else Id.run do
    -- We use the code directly without an indirection a'la `codeMap[t]`.
    let .some tDirect := σ.find? t | ToExecute.Code default
    ToExecute.Code tDirect.code

def L_S (σ : PersistentAccountMap) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      -- dbg_trace s!"Computing L_S; account {EvmYul.toHex addr.toByteArray}"
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState) : ByteArray × ByteArray :=
    (KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

def stateTrieRoot (σ : PersistentAccountMap) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    -- dbg_trace "serializing L_S element"
    let b₁ := EvmYul.toHex entry.1
    let b₂ := EvmYul.toHex entry.2
    (b₁, b₂)

-- instance : LE ((_ : Address) × Account) where
--   le lhs rhs := if lhs.1 = rhs.1 then lhs.2 ≤ rhs.2 else lhs.1 ≤ rhs.1

-- /-
-- Please note that these are used exclusively for conveninece of printing and computing,
-- i.e. the sorries are safe.
-- -/

-- instance : IsTrans ((_ : Address) × Account) (· ≤ ·) := sorry

-- instance : IsAntisymm ((_ : Address) × Account) (· ≤ ·) := sorry

-- instance : IsTotal ((_ : Address) × Account) (· ≤ ·) := sorry

-- instance : DecidableRel (α := (_ : Address) × Account) (· ≤ ·) :=
--   λ lhs rhs ↦ by
--     unfold LE.le instLESigmaAddressAccount
--     exact inferInstance

end RemoveLater

end EvmYul
