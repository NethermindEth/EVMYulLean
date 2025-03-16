import EvmYul.State.Transaction
import EvmYul.State.BlockHeader
import EvmYul.State.ExecutionEnv

namespace EvmYul

def Transaction.to? : Transaction → Option AccountAddress
  -- TODO: Blob transactions can never have `to`
  | .legacy t | .access t | .dynamic t | .blob t => t.recipient

def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t | .blob t => t.data

def GAS_PER_BLOB := 2^17
def VERSIONED_HASH_VERSION_KZG : UInt8 := 1

def getTotalBlobGas (t : Transaction) : ℕ :=
  match t with
  | .blob t => GAS_PER_BLOB * t.blobVersionedHashes.length
  | _ => 0

def Transaction.blobVersionedHashes (t : Transaction) : List ByteArray :=
  match t with
  | .blob t => t.blobVersionedHashes
  | _ => []

def calcBlobFee (header: BlockHeader) (t : Transaction) : ℕ :=
  let totalBlobGas := getTotalBlobGas t
  totalBlobGas * header.getBlobGasprice

end EvmYul
