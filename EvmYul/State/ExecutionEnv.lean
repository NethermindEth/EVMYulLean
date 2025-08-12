import EvmYul.Wheels
import EvmYul.UInt256
import EvmYul.State.BlockHeader
import EvmYul.Yul.Ast

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
structure ExecutionEnv (τ : OperationType) where
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  inputData : ByteArray
  code      : match τ with
                | .EVM => ByteArray
                | .Yul => Yul.Ast.Stmt
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  blobVersionedHashes : List ByteArray

instance {τ} : Inhabited (ExecutionEnv τ) where
  default := {
    codeOwner := default
    sender := default
    source := default
    weiValue := default
    inputData := default
    code := match τ with
              | .EVM => default
              | .Yul => default
    gasPrice := default
    header := default
    depth := default
    perm := default
    blobVersionedHashes := default
  }

def prevRandao (e : ExecutionEnv) : UInt256 :=
  e.header.prevRandao

def basefee (e : ExecutionEnv) : UInt256 :=
  .ofNat e.header.baseFeePerGas

def ExecutionEnv.getBlobGasprice (e : ExecutionEnv) : UInt256 :=
  .ofNat e.header.getBlobGasprice

def blobhash (e : ExecutionEnv) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option ⟨0⟩
    (.ofNat ∘ fromByteArrayBigEndian)

end EvmYul
