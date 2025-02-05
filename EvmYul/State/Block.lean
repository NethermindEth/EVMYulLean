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
deriving BEq, Inhabited, Repr

abbrev Blocks := Array Block

def deserializeBlock (rlp : ByteArray) : Option (BlockHeader × Transactions × Withdrawals) :=
  match deserializeRLP rlp with
    | some (.𝕃 [header, transactions, _, withdrawals]) => do
      let header ← parseHeader header
      let transactions ← parseTransactions transactions
      let withdrawals ← parseWithdrawals withdrawals
      pure (header, Array.mk transactions, Array.mk withdrawals)
    | none =>
      dbg_trace "RLP error: deserializeRLP returned none"
      none
    | _ =>
      dbg_trace "RLP error: deserializeRLP returned wrong rlp structure"
      none
 where
  parseWithdrawal : 𝕋 → Option Withdrawal
    | .𝕃 [.𝔹 globalIndex, .𝔹 validatorIndex, .𝔹 recipient, .𝔹 amount] =>
      pure <|
        .mk
          (.ofNat <| fromByteArrayBigEndian globalIndex)
          (.ofNat <| fromByteArrayBigEndian validatorIndex)
          (.ofNat <| fromByteArrayBigEndian recipient)
          (.ofNat <| fromByteArrayBigEndian amount)
    | _ =>
      dbg_trace "RLP error: parseWithdrawal returns none"
      none
  parseWithdrawals : 𝕋 → Option (List Withdrawal)
    | .𝕃 withdrawals => withdrawals.mapM parseWithdrawal
    | .𝔹 ⟨#[]⟩ => some []
    | _ =>
      dbg_trace "RLP error: parseWithdrawals returns none"
      none

  parseStorageKey : 𝕋 → Option UInt256
    | .𝔹 key => some <| .ofNat <| fromByteArrayBigEndian key
    | _ =>
      dbg_trace "RLP error: parseStorageKey returns none"
      none
  parseAccessListEntry : 𝕋 → Option (AccountAddress × Array UInt256)
    | .𝕃 [.𝔹 accountAddress, .𝕃 storageKeys] => do
      let storageKeys ← storageKeys.mapM parseStorageKey
      let accountAddress : AccountAddress := .ofNat <| fromByteArrayBigEndian accountAddress
      pure (accountAddress, Array.mk storageKeys)
    | _ =>
      dbg_trace "RLP error: parseAccessListEntry returns none"
      none
  parseBlobVersionHash : 𝕋 → Option ByteArray
    | .𝔹 hash => some hash
    | _ =>
      dbg_trace "RLP error: parseBlobVersionHash returns none"
      none
  parseTransaction : 𝕋 → Option Transaction
    | .𝔹 typePlusPayload => -- Transaction type > 0
      match deserializeRLP (typePlusPayload.extract 1 typePlusPayload.size) with
        | some -- Type 3 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 maxFeePerBlobGas
            , .𝕃 blobVersionedHashes
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (.ofNat <| fromByteArrayBigEndian value)
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas := .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas := .ofNat <| fromByteArrayBigEndian maxFeePerGas
            let maxFeePerBlobGas := .ofNat <| fromByteArrayBigEndian maxFeePerBlobGas
            let blobVersionedHashes ← blobVersionedHashes.mapM parseBlobVersionHash
            -- dbg_trace s!" blobVersionedHashes"
            -- _ ← blobVersionedHashes.forM λ bvh ↦
            --   dbg_trace s!"{EvmYul.toHex bvh}"
            --   pure ()
            let dynamicFeeTransaction : DynamicFeeTransaction := .mk base withAccessList maxFeePerGas maxPriorityFeePerGas
            some <| .blob <| BlobTransaction.mk dynamicFeeTransaction maxFeePerBlobGas blobVersionedHashes
        | some -- Type 2 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry
            -- dbg_trace s!" chainId  = {EvmYul.toHex chainId}"
            -- dbg_trace s!" nonce    = {EvmYul.toHex nonce}"
            -- dbg_trace s!" maxPriorityFeePerGas = {EvmYul.toHex maxPriorityFeePerGas}"
            -- dbg_trace s!" maxFeePerGas = {EvmYul.toHex maxFeePerGas}"
            -- dbg_trace s!" gasLimit = {EvmYul.toHex gasLimit}"
            -- dbg_trace s!" recipient: {recipient.map (EvmYul.toHex ∘ BE)}"
            -- dbg_trace s!" value = {EvmYul.toHex value}"
            -- dbg_trace s!" data = {EvmYul.toHex p}"
            -- dbg_trace s!" accestList = {accessList}"
            -- dbg_trace s!" v = {EvmYul.toHex y}"
            -- dbg_trace s!" r: {EvmYul.toHex r}"
            -- dbg_trace s!" s: {EvmYul.toHex s}"

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (.ofNat <| fromByteArrayBigEndian value)
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas := .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas := .ofNat <| fromByteArrayBigEndian maxFeePerGas
            some <| .dynamic <| DynamicFeeTransaction.mk base withAccessList maxPriorityFeePerGas maxFeePerGas
        | some -- Type 1 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 gasPrice
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry
            -- dbg_trace s!" chainId  = {EvmYul.toHex chainId}"
            -- dbg_trace s!" nonce    = {EvmYul.toHex nonce}"
            -- dbg_trace s!" gasPrice = {EvmYul.toHex gasPrice}"
            -- dbg_trace s!" gasLimit = {EvmYul.toHex gasLimit}"
            -- dbg_trace s!" recipient: {recipient.map (EvmYul.toHex ∘ BE)}"
            -- dbg_trace s!" value = {EvmYul.toHex value}"
            -- dbg_trace s!" data = {EvmYul.toHex p}"
            -- dbg_trace s!" accestList = {accessList}"
            -- dbg_trace s!" v = {EvmYul.toHex y}"
            -- dbg_trace s!" r: {EvmYul.toHex r}"
            -- dbg_trace s!" s: {EvmYul.toHex s}"

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (.ofNat <| fromByteArrayBigEndian value)
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
            some <| .access <| AccessListTransaction.mk base withAccessList ⟨gasPrice⟩
        | _ =>
          dbg_trace "RLP error: deserializeRLP could not parse non-legacy transaction"
          none
    | .𝕃
      [ .𝔹 nonce
      , .𝔹 gasPrice
      , .𝔹 gasLimit
      , .𝔹 recipient
      , .𝔹 value
      , .𝔹 p
      , .𝔹 w
      , .𝔹 r
      , .𝔹 s
      ] =>
        let recipient : Option AccountAddress:=
          if recipient.isEmpty then none
          else some <| .ofNat <| fromByteArrayBigEndian recipient
        -- dbg_trace s!"Deserialized legacy transaction"
        -- dbg_trace s!" nonce: {EvmYul.toHex nonce}"
        -- dbg_trace s!" gasPrice: {EvmYul.toHex gasPrice}"
        -- dbg_trace s!" gasLimit: {EvmYul.toHex gasLimit}"
        -- dbg_trace s!" recipient: {recipient.map (EvmYul.toHex ∘ BE)}"
        -- dbg_trace s!" value: {EvmYul.toHex value}"
        -- dbg_trace s!" data: {EvmYul.toHex p}"
        -- dbg_trace s!" w: {EvmYul.toHex w}"
        -- dbg_trace s!" r: {EvmYul.toHex r}"
        -- dbg_trace s!" s: {EvmYul.toHex s}"
        let base : Transaction.Base :=
          Transaction.Base.mk
            (.ofNat <| fromByteArrayBigEndian nonce)
            (.ofNat <| fromByteArrayBigEndian gasLimit)
            recipient
            (.ofNat <| fromByteArrayBigEndian value)
            r
            s
            p
        let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
        let w := .ofNat <| fromByteArrayBigEndian w
        some <| .legacy <| LegacyTransaction.mk base ⟨gasPrice⟩ w
    | _ =>
      dbg_trace "RLP error: parseTransaction returns none"
      none
  parseTransactions : 𝕋 → Option (List Transaction)
    | .𝕃 transactions => transactions.mapM parseTransaction
    | .𝔹 ⟨#[]⟩ => some []
    | _ =>
      dbg_trace "RLP error: parseTransactionS returns none"
      none
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
    | _ =>
      dbg_trace "Block header has wrong RLP structure"
      none

end EvmYul
