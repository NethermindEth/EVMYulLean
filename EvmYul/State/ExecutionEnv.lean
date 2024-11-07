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
  blobVersionedHashes : List ByteArray
  deriving DecidableEq, Inhabited, Repr

def prevRandao (e : ExecutionEnv) : UInt256 :=
  e.header.prevRandao

def basefee (e : ExecutionEnv) : UInt256 :=
  e.header.baseFeePerGas

def ExecutionEnv.getBlobGasprice (e : ExecutionEnv) : UInt256 := e.header.getBlobGasprice

def blobhash (e : ExecutionEnv) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i]?.option 0
    (.ofNat ∘ fromBytesBigEndian ∘ Array.data ∘ ByteArray.data)

end EvmYul
