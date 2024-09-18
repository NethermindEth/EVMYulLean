import Batteries.Data.RBMap

import EvmYul.Maps.AccountMap

import EvmYul.Wheels

import EvmYul.State.Account

namespace EvmYul

abbrev YPState := AccountMap

def YPState.increaseBalance (σ : YPState) (addr : Address) (amount : UInt256)
  : YPState
:=
  match σ.find? addr with
    | none => σ.insert addr {(default : Account) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

end EvmYul
