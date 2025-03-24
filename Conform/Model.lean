import Lean.Data.RBMap
import Lean.Data.Json

-- import EvmYul.Maps
import EvmYul.Operations
import EvmYul.Wheels
import EvmYul.State.Withdrawal
import EvmYul.State.Block

import EvmYul.EVM.State

import Conform.Wheels

namespace EvmYul

namespace Conform

section Model

open Lean

def AddrMap.keys {α : Type} [Inhabited α] (self : AddrMap α) : Multiset AccountAddress :=
  .ofList <| self.toList.map Prod.fst

instance : LE ((_ : UInt256) × UInt256) where
  le lhs rhs := if lhs.1.val = rhs.1.val then lhs.2.val ≤ rhs.2.val else lhs.1.val ≤ rhs.1.val

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

abbrev Code := ByteArray

abbrev Pre := PersistentAccountMap

abbrev PostEntry := PersistentAccountState

abbrev Post := PersistentAccountMap

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

private local instance : Repr Json := ⟨λ s _ ↦ Json.pretty s⟩

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `EVM.State`.
-/

inductive PostState where
  | Hash : ByteArray → PostState
  | Map : Post → PostState
  deriving Inhabited

structure TestEntry where
  info               : Json := ""
  blocks             : RawBlocks
  genesisRLP         : ByteArray
  lastblockhash      : UInt256
  network            : String
  postState          : PostState
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev TestMap := Batteries.RBMap String TestEntry compare

abbrev AccessListEntry := AccountAddress × Array UInt256

abbrev AccessList := Array AccessListEntry

def TestResult := Option String
  deriving Repr, Inhabited

namespace TestResult

def isSuccess (self : TestResult) : Bool := self matches none

def isFailure (self : TestResult) : Bool := !self.isSuccess

def mkFailed (reason : String := "") : TestResult := .some reason

def mkSuccess : TestResult := .none

def ofBool (success : Bool) (reason : String := "Semantics error.") : TestResult :=
  if success then mkSuccess else mkFailed reason

end TestResult

end Model
