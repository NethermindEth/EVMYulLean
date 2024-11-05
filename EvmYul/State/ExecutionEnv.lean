import EvmYul.Wheels
import EvmYul.UInt256
import EvmYul.State.BlockHeader

namespace EvmYul

/--
The execution envorinment `I` `ExecutionEnv`. Section 9.3.
- `codeOwner` `Iₐ`
- `sender`    `Iₒ`
- `source`    `Iₛ`
- `weiValue`  `Iᵥ`
- `inputData` `I_d`
- `code`      `I_b`
- `gasPrice`  `Iₚ`
- `header`    `I_H`
- `depth`     `Iₑ`
- `perm`      `I_w`
-/
structure ExecutionEnv :=
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  inputData : ByteArray
  code      : ByteArray
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  deriving DecidableEq, Inhabited, Repr

def prevRandao (e : ExecutionEnv) : UInt256 :=
  e.header.prevRandao

def basefee (e : ExecutionEnv) : UInt256 :=
  e.header.baseFeePerGas

-- See https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
partial def fakeExponential0 (i output factor numerator denominator : UInt256) : (numeratorAccum : UInt256) → UInt256
  | 0 =>
    output / denominator
  | numeratorAccum =>
    let output := output + numeratorAccum
    let numeratorAccum := (numeratorAccum * numerator) / (denominator * i)
    let i := i + 1
    fakeExponential0 i output factor numerator denominator numeratorAccum

  -- let mut i := 1
  -- let mut output := 1
  -- let numeratorAccum := factor * denominator
  -- for nA in [numeratorAccum : 0] do
  --   sorry
  -- output / denominator

def fakeExponential (factor numerator denominator : UInt256) : UInt256 :=
  fakeExponential0 1 0 factor numerator denominator (factor * denominator)

def MIN_BASE_FEE_PER_BLOB_GAS := 1
def BLOB_BASE_FEE_UPDATE_FRACTION := 3338477

def getBlobGasprice (e : ExecutionEnv) : UInt256 :=
  fakeExponential
    MIN_BASE_FEE_PER_BLOB_GAS
    e.header.excessBlobGas
    BLOB_BASE_FEE_UPDATE_FRACTION

end EvmYul
