import Mathlib.Data.List.AList

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

-- "All transaction types specify a number of common fields:"
/--
`BaseTransaction`. Section 4.3.

- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
TODO: In case of recipient = none, it means contract creation and data should be treated as init?
-/
structure Transaction.Base where
  nonce     : UInt256
  gasLimit  : UInt256
  recipient : Option Address
  value     : UInt256
  r         : ByteArray
  s         : ByteArray
  data      : ByteArray
deriving DecidableEq

-- "EIP-2930 (type 1) and EIP-1559 (type 2) transactions also have:""
/--
`AccessList`. EIP-2930.
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
-/
structure Transaction.WithAccessList where
  chainId : ChainID
  accessList : AList (λ _ : Address ↦ List UInt256)
  yParity : UInt256
deriving DecidableEq

-- "type 0 and type 1 transactions specify gas price as a single value:"
/--
`WithGasPrice`. Section 4.3.
- `gasPrice` `p`
-/
structure Transaction.WithGasPrice where
  gasPrice : UInt256
deriving DecidableEq

-- "Legacy transactions do not have an `accessList`, while `chainId` and `yParity` for legacy transactions are combined into a single value:""
/--
Type 0: `LegacyTransaction`. Section 4.3.
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `gasPrice` `p`
- `w` `w`
-/
structure LegacyTransaction extends Transaction.Base, Transaction.WithGasPrice where
  w: UInt256
deriving DecidableEq

/-- Type 1: `AccessListTransaction`
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
- `gasPrice` `p`
-/
structure AccessListTransaction
  extends Transaction.Base, Transaction.WithAccessList, Transaction.WithGasPrice
deriving DecidableEq

/--
Type 2: `DynamicFeeTransaction`
- `nonce`                `n`
- `gasLimit`             `g`
- `recipinet`            `t`
- `value`                `v`
- `r`                    `r`
- `s`                    `s`
- `data`                 `d/i`
- `chainId`              `c`
- `accessList`           `A`
- `yParity`              `y`
- `maxFeePerGas`         `m`
- `maxPriorityFeePerGas` `f`
-/
structure DynamicFeeTransaction extends Transaction.Base, Transaction.WithAccessList where
  maxFeePerGas         : UInt256
  maxPriorityFeePerGas : UInt256
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
