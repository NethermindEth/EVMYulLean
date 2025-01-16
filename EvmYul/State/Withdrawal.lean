-- Requires the following python packages: pycryptodome

import EvmYul.Wheels
import EvmYul.PerformIO
import EvmYul.Maps.AccountMap
import Conform.Wheels
import EvmYul.EVM.Exception

import EvmYul.State.TrieRoot

open EvmYul ByteArray

/--
EIP-4895: Beacon chain push withdrawals as operations.
- `index` - starting from `0`
- `validator_index`
- `address` - a recipient for the withdrawn ether
- `amount` - a nonzero amount of ether given in Gwei
-/
structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : AccountAddress
  amount : UInt64
deriving Repr, BEq

namespace Withdrawal

def to𝕋 : Withdrawal → 𝕋
  | {index, validatorIndex, address, amount} =>
    .𝕃
      [ .𝔹 (BE index.val.val)
      , .𝔹 (BE validatorIndex.val.val)
      , .𝔹 (address.toByteArray)
      , .𝔹 (BE amount.val.val)
      ]

end Withdrawal

def Withdrawal.toBlobs (w : ℕ × Withdrawal) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  let rlp ← RLP w.2.to𝕋
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
def Withdrawal.computeTrieRoot (ws : Array Withdrawal) : Option ByteArray := do
  match Array.mapM Withdrawal.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def applyWithdrawals
  (σ : AccountMap)
  (ws : Array Withdrawal)
    :
  AccountMap
:=
  ws.foldl applyWithdrawal σ
 where
  applyWithdrawal (σ : AccountMap) (w : Withdrawal) : AccountMap :=
    if w.amount <= 0 then σ else
      match σ.find? w.address with
        | none =>
          σ.insert w.address {(default : Account) with balance := .ofNat <| w.amount.val.val * 10^9}
        | some ac =>
          σ.insert w.address {ac with balance := .ofNat <| ac.balance.toNat + w.amount.val.val * 10^9}

-- Tests

private def withdrawal₁ : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , address := 0x6295ee1b4f6dd65047762f924ecd367c17eabf8f
  , amount := 0x01
  }

private def withdrawal₂ : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , address := 0x000f3df6d732807ef1319fb7b8bb8522d0beac02
  , amount := 0x01
  }

private def withdrawal₃ : Withdrawal :=
  { index := 0x01
  , validatorIndex := 0x01
  , address := 0xfffffffffffffffffffffffffffffffffffffffe
  , amount := 0x01
  }

private def withdrawalZeroTrailingRoot : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , address := 0x0000000000000000000000000000000000000001
  , amount := 0x00
  }

private example :
  (Withdrawal.computeTrieRoot #[])
    ==
  (ByteArray.ofBlob
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
  ).toOption
:= by native_decide

/- From newly_created_contract.json -/
private example :
  (Withdrawal.computeTrieRoot #[withdrawal₁])
    =
  (ByteArray.ofBlob
    "82cc6fbe74c41496b382fcdf25216c5af7bdbb5a3929e8f2e61bd6445ab66436"
  ).toOption
:= by native_decide

/- From beacon_root_contract_deploy.json -/
private example :
  (Withdrawal.computeTrieRoot #[withdrawal₂, withdrawal₃])
    =
  (ByteArray.ofBlob
    "2aef4d3e6939af0b4bf4c0e7572a214eb7db9ba52937e1e82ad6c64b52d2e8bb"
  ).toOption
:= by native_decide

/- From withdrawing_to_precompiles.json -/
private example :
  (Withdrawal.computeTrieRoot #[withdrawalZeroTrailingRoot])
    =
  (ByteArray.ofBlob
    "04cc2e3f94b587ff46b5f4c0787c589db306b7209f7f212f47022a12bc3e6e16"
  ).toOption
:= by native_decide

private def w₀Index : Withdrawal :=
  { address := 0xc94f5374fce5edbc8e2a8697c15331677e6ebf0b
  , amount := 0x2710
  , index := 0x00
  , validatorIndex := 0x00
  }

private def w₁Index : Withdrawal :=
  { address := 0xc94f5374fce5edbc8e2a8697c15331677e6ebf0b
  , amount := 0x2710
  , index := 0x01
  , validatorIndex := 0x00
  }

private def w₂Index : Withdrawal :=
  { address := 0xc94f5374fce5edbc8e2a8697c15331677e6ebf0b
  , amount := 0x2710
  , index := 0x02
  , validatorIndex := 0x0
  }

private example :
  (Withdrawal.computeTrieRoot #[w₀Index, w₂Index, w₁Index, w₂Index])
    =
  (ByteArray.ofBlob
    "a95b9a7b58a6b3cb4001eb0be67951c5517141cb0183a255b5cae027a7b10b36"
  ).toOption
:= by native_decide
