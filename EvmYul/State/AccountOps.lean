import EvmYul.State.Account

import EvmYul.Maps.StorageMap

import EvmYul.Pretty

namespace EvmYul

namespace Account

def lookupStorage (self : Account) (k : UInt256) : UInt256 :=
  self.storage.findD k 0

def updateStorage (self : Account) (k v : UInt256) : Account :=
  { self with storage := self.storage.insert k v }

def lookupTransientStorage (self : Account) (k : UInt256) : UInt256 :=
  self.tstorage.findD k 0

def updateTransientStorage (self : Account) (k v : UInt256) : Account :=
  { self with tstorage := self.tstorage.insert k v }

/--
EMPTY(σ, a). Section 4.1., equation 14.
-/
def emptyAccount (self : Account) : Bool :=
  self.code.isEmpty ∧ self.nonce = 0 ∧ self.balance = 0

def transferBalanceTo (self : Account) (balance : UInt256) (recipient : Account) : Option (Account × Account) :=
  let underflow : Bool := self.balance < balance
  let overflow  : Bool := recipient.balance + balance < recipient.balance
  if underflow || overflow then .none
  else .some (
    {self      with balance := self.balance - balance},
    {recipient with balance := recipient.balance + balance}
  )

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

-- instance : LE Account where
--   le lhs rhs := lhs.storage ≤ rhs.storage

-- instance : DecidableRel (λ (lhs : Account) rhs ↦ lhs ≤ rhs) :=
--   λ lhs rhs ↦ by
--     unfold LE.le instLEAccount
--     exact inferInstance

-- instance : ToString Account := ⟨λ acc ↦ s!"ACCOUNT: {Finmap.pretty acc.storage}"⟩

-- /--
-- TODO - Remove later, debugging.
-- -/
-- private def stringOfStorage (m : Storage) : String := Id.run do
--   let mut result : String := ""
--   for ⟨k, v⟩ in computeToList! m.entries do
--     result := result.append s!"{k} → {v}; "
--   return result

-- instance : ToString Account := ⟨λ acc ↦
--   s!"ACCOUNT: [nonce: {acc.nonce}; balance: {acc.balance}; code: {acc.code.toList.take 5}...; codehash: {acc.codeHash}; storage: {stringOfStorage acc.storage}]; tstorage: {stringOfStorage acc.tstorage}"⟩

-- instance : ToString Account := ⟨λ acc ↦
--   s!"ACCOUNT: storage: {stringOfStorage acc.storage}]"⟩

end RemoveLater

end EvmYul
