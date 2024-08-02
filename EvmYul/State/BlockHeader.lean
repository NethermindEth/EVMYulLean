import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

deriving instance Repr for ByteArray

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
-/
structure BlockHeader where
  parentHash    : UInt256
  ommersHash    : UInt256
  beneficiary   : Address
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
  -- prevRandao -- TODO 
  baseFeePerGas : ℕ
deriving DecidableEq, Inhabited, Repr

attribute [deprecated] BlockHeader.difficulty
attribute [deprecated] BlockHeader.nonce

end EvmYul
