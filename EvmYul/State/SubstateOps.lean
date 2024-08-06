import EvmYul.State.Substate

namespace EvmYul

namespace Substate

def addAccessedAccount (self : Substate) (addr : Address) : Substate :=
  { self with accessedAccounts := self.accessedAccounts.insert addr }

def addAccessedStorageKey (self : Substate) (sk : Address × UInt256) : Substate :=
  { self with accessedStorageKeys := self.accessedStorageKeys.insert sk }

end Substate

end EvmYul
