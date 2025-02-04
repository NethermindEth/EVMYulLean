import Mathlib.Data.Finset.Basic

import EvmYul.State.BlockHeader
import EvmYul.State.Transaction
import EvmYul.State.Withdrawal

namespace EvmYul

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

/--
`Block`. `B<x>`. Section 4.3.
`blockHeader`  `H`
`transactions` `T`
`ommers`       `U` [deprecated]
-/
structure Block where
  blockHeader  : BlockHeader
  rlp          : ByteArray
  transactions : Transactions
  withdrawals  : Withdrawals
  exception    : String
  -- An empty array which was previously reserved for ommer block headers,
  ommers       : Array BlockHeader := ∅
  -- blocknumber  : Nat
  deriving BEq, Inhabited, Repr

attribute [deprecated] Block.ommers

abbrev Blocks := Array Block

def deserializeBlock (rlp : ByteArray) : Option BlockHeader :=
  match deserializeRLP rlp with
    | some (.𝕃 [header, transactions, _, withdrawals]) => do
      let header ← parseHeader header
      pure header
    | _ => none
 where
  parseHeader : 𝕋 → Option BlockHeader
    | .𝕃
      [ .𝔹 parentHash
      , .𝔹 uncleHash
      , .𝔹 coinbase
      , .𝔹 stateRoot
      , .𝔹 transactionsTrie
      , .𝔹 receiptTrie
      , .𝔹 bloom
      , .𝔹 difficulty
      , .𝔹 number
      , .𝔹 gasLimit
      , .𝔹 gasUsed
      , .𝔹 timestamp
      , .𝔹 extraData
      , .𝔹 mixHash
      , .𝔹 nonce
      , .𝔹 baseFeePerGas
      , .𝔹 withdrawalsRoot
      , .𝔹 blobGasUsed
      , .𝔹 excessBlobGas
      , .𝔹 parentBeaconBlockRoot
      ]
      => some <|
        BlockHeader.mk
          (.ofNat <| fromByteArrayBigEndian parentHash)
          (.ofNat <| fromByteArrayBigEndian uncleHash)
          (.ofNat <| fromByteArrayBigEndian coinbase)
          (.ofNat <| fromByteArrayBigEndian stateRoot)
          (.ofNat <| fromByteArrayBigEndian transactionsTrie)
          (.ofNat <| fromByteArrayBigEndian receiptTrie)
          bloom
          (fromByteArrayBigEndian difficulty)
          (fromByteArrayBigEndian number)
          (fromByteArrayBigEndian gasLimit)
          (fromByteArrayBigEndian gasUsed)
          (fromByteArrayBigEndian timestamp)
          extraData
          (.ofNat <| fromByteArrayBigEndian nonce)
          (.ofNat <| fromByteArrayBigEndian mixHash)
          (fromByteArrayBigEndian baseFeePerGas)
          parentBeaconBlockRoot
          (some withdrawalsRoot)
          (some <| .ofNat <| fromByteArrayBigEndian blobGasUsed)
          (some <| .ofNat <| fromByteArrayBigEndian excessBlobGas)
    | _ => none

end EvmYul
