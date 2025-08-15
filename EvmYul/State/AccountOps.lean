import EvmYul.State.Account

import EvmYul.Maps.StorageMap

import EvmYul.Pretty

namespace EvmYul

namespace Account

def lookupStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.storage.findD k ⟨0⟩

def updateStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with storage := self.storage.erase k }
  else
    { self with storage := self.storage.insert k v }

def lookupTransientStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.tstorage.findD k ⟨0⟩

def updateTransientStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with tstorage := self.tstorage.erase k }
  else
    { self with tstorage := self.tstorage.insert k v }

/--
EMPTY(σ, a). Section 4.1., equation 14.
-/
def emptyAccount {τ} (self : Account τ) : Bool :=
  match τ with
    | .EVM => self.code.isEmpty ∧ self.nonce = ⟨0⟩ ∧ self.balance = ⟨0⟩
    | .Yul => false -- Yul statements always hold code.

def addBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let overflow : Bool := self.balance + balance < self.balance
  if overflow then .none
  else .some { self with balance := self.balance + balance }

def subBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let underflow : Bool := self.balance < balance
  if underflow then .none
  else .some { self with balance := self.balance - balance }

end Account

end EvmYul
