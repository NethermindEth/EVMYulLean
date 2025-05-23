import EvmYul.State.Account

import EvmYul.Maps.StorageMap

import EvmYul.Pretty

namespace EvmYul

namespace Account

def lookupStorage (self : Account) (k : UInt256) : UInt256 :=
  self.storage.findD k ⟨0⟩

def updateStorage (self : Account) (k v : UInt256) : Account :=
  if v == default then
    { self with storage := self.storage.erase k }
  else
    { self with storage := self.storage.insert k v }

def lookupTransientStorage (self : Account) (k : UInt256) : UInt256 :=
  self.tstorage.findD k ⟨0⟩

def updateTransientStorage (self : Account) (k v : UInt256) : Account :=
  if v == default then
    { self with tstorage := self.tstorage.erase k }
  else
    { self with tstorage := self.tstorage.insert k v }

/--
EMPTY(σ, a). Section 4.1., equation 14.
-/
def emptyAccount (self : Account) : Bool :=
  self.code.isEmpty ∧ self.nonce = ⟨0⟩ ∧ self.balance = ⟨0⟩

def addBalance (self : Account) (balance : UInt256) : Option Account :=
  let overflow : Bool := self.balance + balance < self.balance
  if overflow then .none
  else .some { self with balance := self.balance + balance }

def subBalance (self : Account) (balance : UInt256) : Option Account :=
  let underflow : Bool := self.balance < balance
  if underflow then .none
  else .some { self with balance := self.balance - balance }

end Account

/-
TODO - For debugging / reporting, likely just remove at some point.
-/

section RemoveLater

instance : ToString Account := ⟨λ acc ↦
  s!"ACCOUNT: storage: {repr acc.storage}"⟩

instance : Repr Account := ⟨λ acc _ ↦ ToString.toString acc⟩

end RemoveLater

end EvmYul
