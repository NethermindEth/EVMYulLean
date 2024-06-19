import Mathlib.Data.List.AList

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
  deriving DecidableEq

/--
`WithGasPriceTransaction`. `T<x>`. Section 4.3.
`gasPrice` `p`
-/
structure WithGasPriceTransaction extends BaseTransaction where
  gasPrice : UInt256
  deriving DecidableEq

/--
`LegacyTransaction`. `T<x>`. Section 4.3.
`w` `w`
-/
structure LegacyTransaction extends WithGasPriceTransaction where
  w: UInt256
  deriving DecidableEq
/--
`LegacyProtectedTransaction`. `T<x>`. Section 4.3.
`chainId` `c`
-/
structure LegacyProtectedTransaction extends LegacyTransaction where
  chainId : ℕ

/--
`AccessListTransaction`. `T<x>`. EIP-2930.
`chainId` `c`
`accessList` `A`
-/
structure AccessListTransaction extends WithGasPriceTransaction where
  chainId : ChainID
  accessList : AList (λ _ : Address ↦ List UInt256)
  deriving DecidableEq

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
  accessList     : AList (λ _ : Address ↦ List UInt256)
  deriving DecidableEq

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  deriving DecidableEq

def Transaction.type : Transaction → Nat
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2

end EvmYul
