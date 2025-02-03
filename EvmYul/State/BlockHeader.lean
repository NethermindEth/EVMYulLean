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
`chainId`       `n` TODO ????
`nonce`         `n` [deprecated]
`baseFeePerGas` `f`
`withdrawalsRoot` (EIP-4895)
`parentBeaconBlockRoot` (EIP-4877)
-/
structure BlockHeader where
  hash          : UInt256
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
  chainId       : UInt256 -- TODO(Why is this here?)
  nonce         : UInt64
  prevRandao    : UInt256
  baseFeePerGas : ℕ
  parentBeaconBlockRoot : ByteArray
  withdrawalsRoot : Option ByteArray
  blobGasUsed     : Option UInt64
  excessBlobGas   : Option UInt64
deriving DecidableEq, Inhabited, Repr, BEq

def TARGET_BLOB_GAS_PER_BLOCK := 393216

def calcExcessBlobGas (parent : BlockHeader) : Option UInt64 := do
  let parentExcessBlobGas ← parent.excessBlobGas
  let parentBlobGasUsed ← parent.blobGasUsed
  if parentExcessBlobGas.toNat + parentBlobGasUsed.toNat < TARGET_BLOB_GAS_PER_BLOCK then
    pure ⟨0⟩
  else
    pure <| .ofNat <| parentExcessBlobGas.toNat + parentBlobGasUsed.toNat - TARGET_BLOB_GAS_PER_BLOCK

-- See https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
partial def fakeExponential0 (i output factor numerator denominator : ℕ) : (numeratorAccum : ℕ) → ℕ
  | 0 =>
    output / denominator
  | numeratorAccum =>
    let output := output + numeratorAccum
    let numeratorAccum := (numeratorAccum * numerator) / (denominator * i)
    let i := i + 1
    fakeExponential0 i output factor numerator denominator numeratorAccum

def fakeExponential (factor numerator denominator : ℕ) : ℕ :=
  fakeExponential0 1 0 factor numerator denominator (factor * denominator)

def MIN_BASE_FEE_PER_BLOB_GAS := 1
def BLOB_BASE_FEE_UPDATE_FRACTION := 3338477

def BlockHeader.getBlobGasprice (h : BlockHeader) : ℕ :=
  fakeExponential
    MIN_BASE_FEE_PER_BLOB_GAS
    (h.excessBlobGas.getD ⟨0⟩).toNat
    BLOB_BASE_FEE_UPDATE_FRACTION

attribute [deprecated] BlockHeader.difficulty
attribute [deprecated] BlockHeader.nonce

end EvmYul
