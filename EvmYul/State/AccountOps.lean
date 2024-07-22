import EvmYul.State.Account

namespace EvmYul

namespace Account

def lookupStorage (self : Account) (k : UInt256) : UInt256 :=
  self.storage.lookup k |>.getD 0

def updateStorage (self : Account) (k v : UInt256) : Account :=
  { self with storage := self.storage.insert k v }

def lookupTransientStorage (self : Account) (k : UInt256) : UInt256 :=
  self.tstorage.lookup k |>.getD 0

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

end EvmYul
