import EvmYul.State.Substate

namespace EvmYul

namespace Substate

def addAccessedAccount (self : Substate) (addr : Address) : Substate :=
  { self with accessedAccounts := {addr} ∪ self.accessedAccounts }

def addAccessedStorageKey (self : Substate) (sk : Address × UInt256) : Substate :=
  { self with accessedStorageKeys := {sk} ∪ self.accessedStorageKeys }

end Substate

end EvmYul
