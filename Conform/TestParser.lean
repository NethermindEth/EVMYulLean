import Lean.Data.Json

import EvmYul.Wheels
import EvmYul.Operations
import EvmYul.EVM.Semantics
import EvmYul.Wheels

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

private def fromBlobString {α} (f : Blob → Except String α) (allowEmpty := false) : FromJson α :=
  {
    fromJson? := λ json ↦ json.getStr? >>= (getBlob?handleEmpty · >>= f)
  }
  where
    emptyBlobOfEmptyString (allowEmpty : Bool) (s : String) : String :=
      if s.isEmpty && allowEmpty then HexPrefix else s
    getBlob?handleEmpty := getBlob? ∘ emptyBlobOfEmptyString allowEmpty

instance : FromJson UInt256 := fromBlobString UInt256.fromBlob?

instance : FromJson Address := fromBlobString Address.fromBlob? (allowEmpty := true)

instance : FromJson Storage where
  fromJson? json := json.getObjVals? Address UInt256

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
  let mut pc := 0
  while pc < code.size do
    let (instr, arg) ← (EVM.decode code pc |>.toExceptWith s!"Cannot decode the instruction: {code.data.get! pc}")
    result := result.push (instr, Prod.fst <$> arg)
    pc := pc + 1 + arg.option 0 Prod.snd
  pure result

end _Code'


/--
TODO - Is this right for both `Code` and general `ByteArray`s?

This is also applicable for `FromJson Code`, as this is an abbrev for `ByteArray`.
-/
instance : FromJson ByteArray := fromBlobString (ByteArray.ofBlob)

instance : FromJson AccountEntry where
  fromJson? json := do
    pure {
      balance := ← json.getObjValAs? UInt256 "balance"
      nonce   := ← json.getObjValAs? UInt256 "nonce"
      code    := ← json.getObjValAs? Code    "code"
      storage := ← json.getObjValAs? Storage "storage"
    }

instance : FromJson Pre where
  fromJson? json := json.getObjVals? Address AccountEntry

instance : FromJson Post where
  fromJson? json := json.getObjVals? Address PostEntry

/--
TODO: We parse ℕ-valued scalars as though they were at most UInt256; could need changing.
-/
instance : FromJson BlockHeader where
  fromJson? json := do
    try
      pure {
        parentHash    := ← json.getObjValAsD! UInt256   "parentHash"
        ommersHash    := TODO -- TODO - Set to whatever the KEC(RLP()) evaluates to.
        beneficiary   := ← json.getObjValAsD! Address   "coinbase"
        stateRoot     := ← json.getObjValAsD! UInt256   "stateRoot"
        transRoot     := TODO -- TODO - Does not seem to be used in Υ?
        receiptRoot   := TODO -- TODO - Does not seem to be used in Υ?
        logsBloom     := ← json.getObjValAsD! ByteArray "bloom"
        difficulty    := 0  -- [deprecated] 0.
        number        := ← json.getObjValAsD! _         "number"        <&> UInt256.toNat
        gasLimit      := ← json.getObjValAsD! _         "gasLimit"      <&> UInt256.toNat
        gasUsed       := ← json.getObjValAsD! _         "gasUsed"       <&> UInt256.toNat
        timestamp     := ← json.getObjValAsD! _         "timestamp"     <&> UInt256.toNat
        extraData     := ← json.getObjValAsD! ByteArray "extraData"
        minHash       := TODO -- TODO - Does not seem to be used in Υ?
        chainId       := 1 -- (5)
        nonce         := 0 -- [deprecated] 0.
        baseFeePerGas := ← json.getObjValAsD! _         "baseFeePerGas" <&> UInt256.toNat
      }
    catch exct => dbg_trace s!"OOOOPSIE: {exct}\n json: {json}"
                  default

instance : FromJson AccessListEntry where
  fromJson? json := do
    pure {
      address     := ← json.getObjValAs? Address         "address"
      storageKeys := ← json.getObjValAs? (Array UInt256) "storageKeys"
    }

/--
TODO - Currently we return `AccessListTransaction`. No idea if this is what we want.
-/
instance : FromJson Transaction where
  fromJson? json := do
    let baseTransaction : Transaction.Base := {
      nonce     := ← json.getObjValAsD! UInt256          "nonce"
      gasLimit  := ← json.getObjValAsD! UInt256          "gasLimit"
      recipient := ← json.getObjValAsD! (Option Address) "to" -- TODO - How do tests represent no 'to' - just missing field? Refine this.
      value     := ← json.getObjValAsD! UInt256          "value"
      r         := ← json.getObjValAsD! ByteArray        "r"
      s         := ← json.getObjValAsD! ByteArray        "s"
      data      := ← json.getObjValAsD! ByteArray        "data"
    }

    match json.getObjVal? "w" with
      | .ok w => do
        return .legacy ⟨baseTransaction, ⟨← json.getObjValAsD! UInt256 "gasPrice"⟩, ← FromJson.fromJson? w⟩
      | .error _ => do
        -- Any other transaction now necessarily has an access list.
        let accessListTransaction : Transaction.WithAccessList :=
          { 
            chainId    := let mainnet : Nat := 1; mainnet
            accessList := ← json.getObjValAsD! _ "accessList" <&> accessListToRBMap
            yParity    := TODO
          }

        match json.getObjVal? "w" with
          | .ok gasPrice => do
            return .access ⟨baseTransaction, accessListTransaction, ⟨← FromJson.fromJson? gasPrice⟩⟩
          | .error _ =>
            return .dynamic ⟨
                     baseTransaction,
                     accessListTransaction,
                     ← json.getObjValAsD! UInt256 "maxFeePerGas",
                     ← json.getObjValAsD! UInt256 "maxPriorityFeePerGas"
                   ⟩

  where accessListToRBMap (this : AccessList) : Batteries.RBMap Address (Array UInt256) compare :=
    this.foldl (init := ∅) λ m ⟨addr, list⟩ ↦ m.insert addr list

/--
- Format₀: `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json`
- Format₁: `EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/invalid_static_excess_blob_gas.json`

TODO - 
- `EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/invalid_blob_tx_contract_creation.json` - ?????
-/
private def blockEntryOfJson (json : Json) : Except String BlockEntry := do
  -- The exception, if exists, is always in the outermost object regardless of the `<Format>` (see this function's docs).
  let exception ← json.getObjValAsD! String "expectException"
  -- Descend to `rlp_decoded` - Format₁ if exists, Format₀ otherwise.
  let json ← json.getObjValAsD Json "rlp_decoded" json
  pure {
    blockHeader  := ← json.getObjValAsD! BlockHeader  "blockHeader"
    rlp          := ← json.getObjValAsD! Json         "rlp"
    transactions := ← json.getObjValAsD! Transactions "transactions"
    uncleHeaders := ← json.getObjValAsD! Json         "uncleHeaders"
    withdrawals  := ← json.getObjValAsD! Json         "withdrawals"
    blocknumber  := ← json.getObjValAsD  _            "blocknumber" "1" >>= tryParseBlocknumber
    exception    := exception
  }
  where
    tryParseBlocknumber (s : String) : Except String Nat := 
      s.toNat?.elim (.error "Cannot parse `blocknumber`.") .ok

instance : FromJson BlockEntry := ⟨blockEntryOfJson⟩

deriving instance FromJson for TestEntry

instance : FromJson Test where
  fromJson? json := json.getObjVals? String TestEntry

end FromJson

def testNamesOfTest (test : Lean.Json) : Except String (Array String) :=
  test.getObj? <&> (·.toArray.map Sigma.fst)

namespace Test

end Test

section PrettyPrinter

instance : ToString AccountEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Pre := ⟨ToString.toString ∘ repr⟩

instance : ToString PostEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Post := ⟨ToString.toString ∘ repr⟩

instance : ToString AccessListEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Transaction := ⟨λ _ ↦ "Some transaction."⟩

end PrettyPrinter

end Parser

end Conform

end EvmYul
