import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
`BlockHeader`. `H_<x>`. Section 4.3.

`parentHash`    `p`
`ommersHash`    `o`
`beneficiary`   `c`
`stateRoot`     `r`
`transRoot`     `t`
`receiptRoot`   `e`
`logsBloom`     `b`
`difficulty`    `d` [deprecated]
`number`        `i`
`gasLimit`      `l`
`gasUsed`       `g`
`timestamp`     `s`
`extraData`     `x`
`minHash`       `m`
`chainId`       `n` TODO ????
`nonce`         `n` [deprecated]
`baseFeePerGas` `f`
`withdrawalsRoot` (EIP-4895)
`parentBeaconBlockRoot` (EIP-4877)
-/
structure BlockHeader where
  parentHash    : UInt256
  ommersHash    : UInt256
  beneficiary   : AccountAddress
  stateRoot     : UInt256
  transRoot     : UInt256
  receiptRoot   : UInt256
  logsBloom     : ByteArray
  difficulty    : ℕ
  number        : ℕ
  gasLimit      : ℕ
  gasUsed       : ℕ
  timestamp     : ℕ
  extraData     : ByteArray
  minHash       : UInt256
  chainId       : UInt256 -- TODO(Why is this here?)
  nonce         : UInt64
  prevRandao    : UInt256
  baseFeePerGas : ℕ
  parentBeaconBlockRoot : ByteArray
  withdrawalsRoot : ByteArray
deriving DecidableEq, Inhabited, Repr

attribute [deprecated] BlockHeader.difficulty
attribute [deprecated] BlockHeader.nonce
/-
  We return a presudorandom value instead of fetching this field.
-/
attribute [deprecated] BlockHeader.prevRandao

end EvmYul
