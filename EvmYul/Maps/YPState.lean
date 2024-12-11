import Batteries.Data.RBMap

import EvmYul.Maps.AccountMap

import EvmYul.Wheels

import EvmYul.State.Account

namespace EvmYul

-- def AccountMap.increaseBalance (σ : AccountMap) (addr : AccountAddress) (amount : UInt256)
--   : AccountMap
-- :=
--   match σ.find? addr with
--     | none => σ.insert addr {(default : Account) with balance := amount}
--     | some acc => σ.insert addr {acc with balance := acc.balance + amount}

end EvmYul
