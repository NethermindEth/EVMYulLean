import Batteries.Data.RBMap

import EvmYul.Wheels

import EvmYul.State.Account

namespace EvmYul

abbrev YPState := Batteries.RBMap Address Account compare

end EvmYul
