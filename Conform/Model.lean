import Lean.Data.RBMap
import Lean.Data.Json

-- import EvmYul.Maps
import EvmYul.Operations
import EvmYul.Wheels

import EvmYul.EVM.State

import Conform.Wheels

import Mathlib.Tactic

namespace EvmYul

namespace Conform

section Model

open Lean

abbrev AddrMap (α : Type) [Inhabited α] := Lean.RBMap Address α compare
abbrev Storage := AddrMap UInt256

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.fold (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def Storage.toEvmYulStorage (self : Storage) : EvmYul.Storage :=
  self.fold (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def AddrMap.keys {α : Type} [Inhabited α] (self : AddrMap α) : Multiset Address :=
  .ofList <| self.toList.map Prod.fst

instance : LE ((_ : UInt256) × UInt256) where
  le lhs rhs := if lhs.1 = rhs.1 then lhs.2 ≤ rhs.2 else lhs.1 ≤ rhs.1

instance : IsTrans ((_ : UInt256) × UInt256) (· ≤ ·) where
  trans a b c h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    rcases c with ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
    unfold LE.le instLESigmaUInt256_conform at h₁ h₂ ⊢; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsAntisymm ((_ : UInt256) × UInt256) (· ≤ ·) where
  antisymm a b h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform at h₁ h₂; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsTotal ((_ : UInt256) × UInt256) (· ≤ ·) where
  total a b := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform; simp
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : DecidableRel (α := (_ : UInt256) × UInt256) (· ≤ ·) :=
  λ a b ↦ by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform; simp
    aesop (config := {warnOnNonterminal := false}) <;> exact inferInstance

def Storage.ofFinmap (m : EvmYul.Storage) : Storage :=
  Lean.RBMap.ofList <| m.toList.map λ (k, v) ↦ (Address.ofUInt256 k, v)

abbrev Code := ByteArray

structure AccountEntry :=
  balance : UInt256
  code    : ByteArray
  nonce   : UInt256
  storage : Storage
  deriving Inhabited, Repr

abbrev Pre := AddrMap AccountEntry

abbrev PostEntry := AccountEntry

abbrev Post := AddrMap PostEntry

abbrev Transactions := Array Transaction

/--
TODO - Temporary.
-/
private local instance : Repr Json := ⟨λ s _ ↦ Json.pretty s⟩ 

structure BlockEntry :=
  blockHeader  : BlockHeader
  rlp          : Json
  transactions : Transactions
  uncleHeaders : Json
  withdrawals  : Json
  exception    : String -- TODO - I am guessing there is a closed set of these to turn into a sum.
  blocknumber  : Nat
  deriving Inhabited, Repr

abbrev Blocks := Array BlockEntry

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `EVM.State`.

This would be ever so slightly cleaner, but before we understand the exact correlation
between all of the test file entires and the states, we sometimes keep a 'parsing model' *and*
an EVM model and write translations between them where convenient.
-/
structure TestEntry :=
  info               : Json := ""
  blocks             : Blocks
  genesisBlockHeader : Json := ""
  genesisRLP         : Json := ""
  lastblockhash      : Json := ""
  network            : Json := ""
  postState          : Post
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev Test := Lean.RBMap String TestEntry compare 

structure AccessListEntry :=
  address     : Address
  storageKeys : Array UInt256
  deriving Inhabited, Repr

abbrev AccessList := Array AccessListEntry

def TestResult := Option String
  deriving Repr

namespace TestResult

def isSuccess (self : TestResult) : Bool := self matches none

def isFailure (self : TestResult) : Bool := !self.isSuccess

def mkFailed (reason : String := "") : TestResult := .some reason

def mkSuccess : TestResult := .none

def ofBool (success : Bool) (reason : String := "Semantics error.") : TestResult :=
  if success then mkSuccess else mkFailed reason

end TestResult

end Model
