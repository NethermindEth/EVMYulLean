import Batteries.Data.RBMap

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
`BaseTransaction`. `T<x>`. Section 4.3.

`nonce`     `x`
`gasLimit` `a`
`recipinet` `g`
`value`     `t`
`r`         `s`
`s`         `r`
`data`      `d/i`
TODO: In case of recipient = none, it means contract creation and data should be treated as init?
-/
structure BaseTransaction where
  nonce     : UInt256
  gasLimit  : UInt256
  recipient : Option Address 
  value     : UInt256
  r         : ByteArray
  s         : ByteArray
  data      : ByteArray
  deriving DecidableEq, Repr

/--
`WithGasPriceTransaction`. `T<x>`. Section 4.3.
`gasPrice` `p`
-/
structure WithGasPriceTransaction extends BaseTransaction where
  gasPrice : UInt256
  deriving DecidableEq, Repr

/--
`LegacyTransaction`. `T<x>`. Section 4.3.
`w` `w`
-/
structure LegacyTransaction extends WithGasPriceTransaction where
  w: UInt256
  deriving DecidableEq, Repr
/--
`LegacyProtectedTransaction`. `T<x>`. Section 4.3.
`chainId` `c`
-/
structure LegacyProtectedTransaction extends LegacyTransaction where
  chainId : ℕ
  deriving Repr

/--
`AccessListTransaction`. `T<x>`. EIP-2930.
`chainId` `c`
`accessList` `A`
-/
structure AccessListTransaction extends WithGasPriceTransaction where
  chainId : ChainID
  accessList : Batteries.RBMap Address (Array UInt256) compare
  deriving BEq, Repr

/--
`DynamicFeeTransaction`. `T<x>`. EIP-1559.

`priorityGasFee` 
`maxGasFee`      
`chainId`    `c`
`accessList` `A`
-/
structure DynamicFeeTransaction extends BaseTransaction where
  priorityGasFee : UInt256
  maxGasFee      : UInt256
  chainId        : ChainID
  accessList     : Batteries.RBMap Address (Array UInt256) compare
  deriving BEq, Repr

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  deriving BEq, Repr

def Transaction.type : Transaction → Nat
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2

end EvmYul
