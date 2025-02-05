import Lean.Data.Json

import EvmYul.Wheels
import EvmYul.Operations
import EvmYul.EVM.Semantics
import EvmYul.Wheels
import EvmYul.State.Withdrawal

import Conform.Model
import Conform.Wheels

namespace EvmYul

namespace Conform

namespace Parser

section FromJson

open Lean (FromJson Json)

/--
Sorries are often
-/
@[deprecated]
scoped notation "TODO" => default

private def fromBlobString {α} (f : Blob → Except String α) : FromJson α :=
  {
    fromJson? := λ json ↦ json.getStr? >>= (getBlob? · >>= f)
  }

instance : FromJson UInt256 := fromBlobString UInt256.fromBlob?
instance : FromJson ℕ := fromBlobString Nat.fromBlob?

instance : FromJson AccountAddress := fromBlobString AccountAddress.fromBlob?

instance : FromJson Storage where
  fromJson? json := json.getObjVals? UInt256 UInt256

section _Code'
-- The `_Code'` section is auxiliary and the functionality inside is currently unused.

/--
We probably want to fetch/decode on demand, as such, `Conform.Code` can be a `ByteArray`.
Keep this around for potential convenience.
-/
abbrev Code' := Array (Operation .EVM × Option UInt256)

/--
Decode `ByteArray` to an array of `Operation`s. Considering we do decoding on demand,
this is only kept around for potential conveninece.

TODO: This is essentially `unfold` with `f := EVM.decode code`.
Why is there no handy `unfold` - because of termination issues?
-/
def decodeMany (code : ByteArray) : Except String Code' := do
  let mut result : Code' := #[]
  let mut pc : UInt256 := ⟨0⟩
  while pc.toNat < code.size do
    let (instr, arg) ← (EVM.decode code pc |>.toExceptWith s!"Cannot decode the instruction: {code.data.get! pc.toNat}")
    result := result.push (instr, Prod.fst <$> arg)
    pc := pc + .ofNat (1 + arg.option 0 Prod.snd)
  pure result

end _Code'


/--
TODO - Is this right for both `Code` and general `ByteArray`s?

This is also applicable for `FromJson Code`, as this is an abbrev for `ByteArray`.
-/
instance : FromJson ByteArray := fromBlobString (ByteArray.ofBlob)

instance : FromJson PersistentAccountState where
  fromJson? json := do
    pure {
      balance := ← json.getObjValAs? UInt256 "balance"
      nonce   := ← json.getObjValAs? UInt256 "nonce"
      code    := ← json.getObjValAs? Code    "code"
      storage := ← json.getObjValAs? Storage "storage"
    }

instance : FromJson Pre where
  fromJson? json := json.getObjVals? AccountAddress PersistentAccountState

instance : FromJson Post where
  fromJson? json := json.getObjVals? AccountAddress PostEntry

/--
TODO: We parse ℕ-valued scalars as though they were at most UInt256; could need changing.
-/
instance : FromJson BlockHeader where
  fromJson? json := do
    try
      pure {
        parentHash    := ← json.getObjValAsD! UInt256   "parentHash"
        ommersHash    := ← json.getObjValAsD! UInt256   "uncleHash"
        beneficiary   := ← json.getObjValAsD! AccountAddress   "coinbase"
        stateRoot     := ← json.getObjValAsD! UInt256   "stateRoot"
        transRoot     := ← json.getObjValAsD! UInt256   "transactionsTrie"
        receiptRoot   := ← json.getObjValAsD! UInt256   "receiptTrie"
        logsBloom     := ← json.getObjValAsD! ByteArray "bloom"
        difficulty    := 0  -- [deprecated] 0.
        number        := ← json.getObjValAsD! ℕ         "number"
        gasLimit      := ← json.getObjValAsD! ℕ         "gasLimit"
        gasUsed       := ← json.getObjValAsD! ℕ         "gasUsed"
        timestamp     := ← json.getObjValAsD! ℕ         "timestamp"
        extraData     := ← json.getObjValAsD! ByteArray "extraData"
        nonce         := 0 -- [deprecated] 0.
        baseFeePerGas := ← json.getObjValAsD! ℕ         "baseFeePerGas"
        parentBeaconBlockRoot := ← json.getObjValAsD! ByteArray "parentBeaconBlockRoot"
        prevRandao    := ← json.getObjValAsD! UInt256 "mixHash"
        withdrawalsRoot := ← json.getObjValAsD! (Option ByteArray) "withdrawalsRoot"
        blobGasUsed    := ← json.getObjValAsD! (Option UInt64) "blobGasUsed"
        excessBlobGas    := ← json.getObjValAsD! (Option UInt64) "excessBlobGas"
      }
    catch exct => dbg_trace s!"OOOOPSIE: {exct}\n json: {json}"
                  default

instance : FromJson AccessListEntry where
  fromJson? json := do
    let address     := ← json.getObjValAs? AccountAddress "address"
    let storageKeys := ← json.getObjValAs? (Array UInt256) "storageKeys"
    pure (address, storageKeys)

instance : FromJson Withdrawal where
  fromJson? json := do
    pure {
      index     := ← json.getObjValAs? UInt64         "index"
      validatorIndex := ← json.getObjValAs? UInt64 "validatorIndex"
      address := ← json.getObjValAs? AccountAddress "address"
      amount := ← json.getObjValAs? UInt64 "amount"
    }

/--
TODO - Currently we return `AccessListTransaction`. No idea if this is what we want.
-/
instance : FromJson Transaction where
  fromJson? json := do
    let baseTransaction : Transaction.Base := {
      nonce          := ← json.getObjValAsD! UInt256        "nonce"
      gasLimit       := ← json.getObjValAsD! UInt256        "gasLimit"
      recipient      := ← match json.getObjVal? "to" with
                          | .error _ => .ok .none
                          | .ok ok => do let str ← ok.getStr?
                                         if str.isEmpty then .ok .none else FromJson.fromJson? str
      value          := ← json.getObjValAsD! UInt256        "value"
      r              := ← json.getObjValAsD! ByteArray      "r"
      s              := ← json.getObjValAsD! ByteArray      "s"
      data           := ← json.getObjValAsD! ByteArray      "data"
      -- expectedSender := ← json.getObjValAsD! AccountAddress "sender"
    }

    match json.getObjVal? "accessList" with
      | .error _ => do
        return .legacy ⟨baseTransaction, ⟨← json.getObjValAsD! UInt256 "gasPrice"⟩, ← json.getObjValAsD! UInt256 "v"⟩
      | .ok accessList => do
        -- Any other transaction now necessarily has an access list.
        let accessListTransaction : Transaction.WithAccessList :=
          {
            chainId    := ← json.getObjValAsD UInt256 "chainId" ⟨1⟩
            accessList := ← FromJson.fromJson? accessList
            yParity    := ← json.getObjValAsD! UInt256 "v"
          }

        match json.getObjVal? "gasPrice" with
          | .ok gasPrice => do
            -- dbg_trace "Constructing an access transaction."
            return .access ⟨baseTransaction, accessListTransaction, ⟨← FromJson.fromJson? gasPrice⟩⟩
          | .error _ =>
            let dynamic : DynamicFeeTransaction :=
              ⟨ baseTransaction
              , accessListTransaction
              , ← json.getObjValAsD! UInt256 "maxFeePerGas"
              , ← json.getObjValAsD! UInt256 "maxPriorityFeePerGas"
              ⟩
            match json.getObjVal? "maxFeePerBlobGas" with
            | .error _ =>
              pure <| .dynamic dynamic
            | .ok maxFeePerBlobGas =>
              -- dbg_trace "Constructing a BLOB transaction."
              pure <|
                .blob
                  ⟨ dynamic
                  , ← FromJson.fromJson? maxFeePerBlobGas
                  , ← json.getObjValAsD! (List ByteArray) "blobVersionedHashes"
                  ⟩



-- #eval DebuggingAndProfiling.testJsonParser Transaction r#"
--                     {
--                         "data" : "0x6001600155601080600c6000396000f3006000355415600957005b60203560003555",
--                         "gasLimit" : "0x1314e0",
--                         "gasPrice" : "0x0a",
--                         "nonce" : "0x00",
--                         "r" : "0x519086556db928a3f679b49fc6211c84896a75312c52e7e05a3b5041f59bb49d",
--                         "s" : "0x70c4b1df7933a7aa4717c13ab34cc2b02daae23ca33836652e526a6a61de0681",
--                         "sender" : "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b",
--                         "to" : "",
--                         "v" : "0x1b",
--                         "value" : "0x0186a0"
--                     }"#

/--
- Format₀: `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json`
- Format₁: `EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/invalid_static_excess_blob_gas.json`
-/
private def blockOfJson (json : Json) : Except String RawBlock := do
  -- The exception, if exists, is always in the outermost object regardless of the `<Format>` (see this function's docs).
  let exception ← json.getObjValAsD! String "expectException"
  let rlp          := ← json.getObjValAsD! ByteArray "rlp"
  -- Descend to `rlp_decoded` - Format₁ if exists, Format₀ otherwise.
  let json ← json.getObjValAsD Json "rlp_decoded" json
  pure {
    rlp
    blockHeader  := ← json.getObjValAsD! (Option BlockHeader) "blockHeader"
    transactions := ← json.getObjValAsD! (Option Transactions) "transactions"
    withdrawals  := ← json.getObjValAsD! (Option Withdrawals) "withdrawals"
    exception    := exception
  }
  where
    tryParseBlocknumber (s : String) : Except String Nat :=
      s.toNat?.elim (.error "Cannot parse `blocknumber`.") .ok

instance : FromJson RawBlock := ⟨blockOfJson⟩

-- instance : FromJson PostState where
--   fromJson? json := do
--     let hash ← json.getObjValAsD! (Option ByteArray) "postStateHash"
--     match hash with
--       | some hash =>
--         dbg_trace s!"Read postStateHash: {hash}"
--         .ok <| PostState.Hash hash
--       | none =>
--         let map ← json.getObjValAsD! Post "postState"
--         dbg_trace s!"Read post state map of size {map.size}"
--         .ok <| PostState.Map map

instance : FromJson RawTestEntry where
  fromJson? json := do
    let post : PostState ←
      match json.getObjVal? "postStateHash" with
        | .error _ =>
          -- dbg_trace s!"Read post state map"
          .Map <$> json.getObjValAsD! PersistentAccountMap "postState"
        | .ok postStateHash =>
          -- dbg_trace s!"Read postStateHash: {postStateHash}"
          .Hash <$> FromJson.fromJson? postStateHash
    pure {
      info               := ← json.getObjValAs? Json "info"
      blocks             := ← json.getObjValAs? RawBlocks "blocks"
      genesisBlockHeader := ← json.getObjValAs? BlockHeader "genesisBlockHeader"
      genesisRLP         := ← json.getObjValAs? Json "genesisRLP"
      lastblockhash      := ← json.getObjValAs? Json "lastblockhash"
      network            := ← json.getObjValAs? String "network"
      postState          := post
      pre                := ← json.getObjValAs? Pre "pre"
      sealEngine         := ← json.getObjValAs? Json "sealEngine"
    }

instance : FromJson RawTestMap where
  fromJson? json := json.getObjVals? String RawTestEntry

end FromJson

def testNamesOfTest (test : Lean.Json) : Except String (Array String) :=
  test.getObj? <&> (·.toArray.map Sigma.fst)

section PrettyPrinter

instance : ToString PersistentAccountState := ⟨ToString.toString ∘ repr⟩

instance : ToString Pre := ⟨ToString.toString ∘ repr⟩

instance : ToString PostEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Post := ⟨ToString.toString ∘ repr⟩

instance : ToString AccessListEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Transaction := ⟨λ _ ↦ "Some transaction."⟩

end PrettyPrinter

end Parser

end Conform

end EvmYul
