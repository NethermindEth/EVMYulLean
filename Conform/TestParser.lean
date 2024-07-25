import Lean.Data.Json

import EvmYul.Wheels
import EvmYul.Operations
import EvmYul.EVM.Semantics

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

instance : FromJson Address := fromBlobString Address.fromBlob?

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
        parentHash    := ← json.getObjValAsOrInit? UInt256   "parentHash"
        ommersHash    := TODO -- TODO - Set to whatever the KEC(RLP()) evaluates to.
        beneficiary   := TODO
        stateRoot     := ← json.getObjValAsOrInit? UInt256   "stateRoot"
        transRoot     := TODO
        receiptRoot   := TODO
        logsBloom     := ← json.getObjValAsOrInit? ByteArray "bloom"
        difficulty    := 0  -- [deprecated] 0.
        number        := ← json.getObjValAsOrInit? _         "number"        <&> UInt256.toNat
        gasLimit      := ← json.getObjValAsOrInit? _         "gasLimit"      <&> UInt256.toNat
        gasUsed       := ← json.getObjValAsOrInit? _         "gasUsed"       <&> UInt256.toNat
        timestamp     := ← json.getObjValAsOrInit? _         "timestamp"     <&> UInt256.toNat
        extraData     := ← json.getObjValAsOrInit? ByteArray "extraData"
        minHash       := TODO
        chainId       := TODO
        nonce         := 0  -- [deprecated] 0.
        baseFeePerGas := ← json.getObjValAsOrInit? _         "baseFeePerGas" <&> UInt256.toNat
      }
    catch exct => dbg_trace s!"OOOOPSIE: {exct}\n json: {json}"
                  default

/--
TODO - Currently we return `AccessListTransaction`. No idea if this is what we want.
-/
instance : FromJson Transaction where
  fromJson? json := do
    pure <| .access {
      nonce      := ← json.getObjValAs? UInt256          "nonce"
      gasLimit   := ← json.getObjValAs? UInt256          "gasLimit"
      recipient  := ← json.getObjValAs? (Option Address) "to" -- TODO - How do tests represent no 'to' - just missing field? Refine this.
      value      := ← json.getObjValAs? UInt256          "value"
      r          := ← json.getObjValAs? ByteArray        "r"
      s          := ← json.getObjValAs? ByteArray        "s"
      data       := ← json.getObjValAs? ByteArray        "data"
      gasPrice   := ← json.getObjValAs? UInt256          "gasPrice"
      chainId    := TODO
      accessList := TODO -- TODO - Not sure this needs initialising in tests.
    }

instance : FromJson BlockEntry where
  fromJson? json := do
    pure {
      blockHeader  := ← json.getObjValAs? BlockHeader  "blockHeader"
      rlp          := ← json.getObjValAs? Json         "rlp"
      transactions := ← json.getObjValAs? Transactions "transactions"
      uncleHeaders := ← json.getObjValAs? Json         "uncleHeaders"
      withdrawals  := ← json.getObjValAs? Json         "withdrawals"
    }

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

instance : ToString Transaction := ⟨λ _ ↦ "Some transaction."⟩

end PrettyPrinter

end Parser

end Conform

end EvmYul
