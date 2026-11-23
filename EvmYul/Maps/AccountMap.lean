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

import EvmYul.Maps.StorageMap

import EvmYul.State.Account
import EvmYul.State.AccountOps

namespace EvmYul

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Std.TreeMap AccountAddress α compare
abbrev AccountMap (τ : OperationType) := AddrMap (Account τ)
abbrev PersistentAccountMap (τ : OperationType) := AddrMap (PersistentAccountState τ)
def AccountMap.toPersistentAccountMap (τ : OperationType) (a : AccountMap τ) : PersistentAccountMap τ :=
  a.map (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : AccountMap τ
:=
  match σ.get? addr with
    | none => σ.insert addr {(default : Account τ) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.decreaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match σ.get? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (σ.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.transferBalance (τ : OperationType) (σ : AccountMap τ) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match (σ.decreaseBalance τ from_addr amount) with
    | .none => .none
    | .some σ' => σ'.increaseBalance τ to_addr amount

def toExecute (τ : OperationType) (σ : AccountMap τ) (t : AccountAddress) : ToExecute τ :=
  if /- t is a precompiled account -/ t ∈ π then
    ToExecute.Precompiled t
  else Id.run do
    match τ with
      | .EVM =>
        -- We use the code directly without an indirection a'la `codeMap[t]`.
        let .some tDirect := σ.get? t | ToExecute.Code default
        ToExecute.Code tDirect.code
      | .Yul =>
        let .some tDirect := σ.get? t | ToExecute.Code default
        ToExecute.Code tDirect.code

def L_S (σ : PersistentAccountMap .EVM) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState .EVM) : ByteArray × ByteArray :=
    (ffi.KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState .EVM) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

def stateTrieRoot (σ : PersistentAccountMap .EVM) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    let b₁ := EvmYul.toHex entry.1
    let b₂ := EvmYul.toHex entry.2
    (b₁, b₂)

end RemoveLater

end EvmYul
