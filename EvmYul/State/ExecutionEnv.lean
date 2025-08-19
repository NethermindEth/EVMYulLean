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
                | .Yul => Finmap (fun (_ : String) ↦ Yul.Ast.FunctionDefinition)
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  blobVersionedHashes : List ByteArray

instance {τ} [Repr (match τ with | .EVM => ByteArray | .Yul => Finmap (fun (_ : String) ↦ Yul.Ast.FunctionDefinition))] : Repr (ExecutionEnv τ) where
  reprPrec e _ :=
    let codeFmt :=
      match τ with
      | .EVM => reprPrec e.code 0
      | .Yul => reprPrec e.code 0
    s!"ExecutionEnv(codeOwner: {reprPrec e.codeOwner 0}, sender: {reprPrec e.sender 0}, source: {reprPrec e.source 0}, weiValue: {reprPrec e.weiValue 0}, inputData: {reprPrec e.inputData 0}, code: {codeFmt}, gasPrice: {reprPrec e.gasPrice 0}, header: {reprPrec e.header 0}, depth: {reprPrec e.depth 0}, perm: {reprPrec e.perm 0}, blobVersionedHashes: {reprPrec e.blobVersionedHashes 0})"

-- instance : BEq (Finmap (fun (_ : String) ↦ Yul.Ast.FunctionDefinition)) where
--   beq a b := a.keys == b.keys &&
--       a.all (λ k _ => a.lookup k == b.lookup k)

instance {τ} : BEq (ExecutionEnv τ) where
  beq a b :=
       a.codeOwner == b.codeOwner
    && a.sender == b.sender
    && a.source == b.source
    && a.weiValue == b.weiValue
    && a.inputData == b.inputData
    && (match τ with
          | .EVM => a.code == b.code
          | .Yul => (a.code.keys == b.code.keys &&
                       a.code.all (λ k _ => a.code.lookup k == b.code.lookup k)))
    && a.gasPrice == b.gasPrice
    && a.header == b.header
    && a.depth == b.depth
    && a.perm == b.perm
    && a.blobVersionedHashes == b.blobVersionedHashes

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

def prevRandao {τ} (e : ExecutionEnv τ) : UInt256 :=
  e.header.prevRandao

def basefee {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.baseFeePerGas

def ExecutionEnv.getBlobGasprice {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.getBlobGasprice

def blobhash {τ} (e : ExecutionEnv τ) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option ⟨0⟩
    (.ofNat ∘ fromByteArrayBigEndian)

end EvmYul
