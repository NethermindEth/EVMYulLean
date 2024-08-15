-- Requires the following python packages: pycryptodome

import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

open EvmYul ByteArray

structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  recipient : Address
  amount : UInt64

namespace Withdrawal

def to𝕋 : Withdrawal → 𝕋
  | {index, validatorIndex, recipient, amount} =>
    .𝕃
      [ .𝔹 (BE index.val.val)
      , .𝔹 (BE validatorIndex.val.val)
      , .𝔹 (recipient.toByteArray)
      , .𝔹 (BE amount.val.val)
      ]

end Withdrawal

def blobComputeTrieRoot (ws : List (String × String)) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput ws
  where pythonCommandOfInput (ws : List (String × String)) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args :=
      #["EvmYul/EllipticCurvesPy/withdrawal.py"]
        ++ #[ws.length.repr]
        ++ .mk (List.join ∘ List.map (λ (i, w) ↦ [i, w]) <| ws)
  }

def toBlobs (w : Withdrawal) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.index.val))
  let rlp ← RLP w.to𝕋
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
def computeTrieRoot (ws : List Withdrawal) : Except String ByteArray := do
  match List.traverse toBlobs ws with
    | none => .error "Could not encode withdrawal."
    | some ws => ByteArray.ofBlob (blobComputeTrieRoot ws)

-- Tests

private def withdrawal₁ : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , recipient := 0x6295ee1b4f6dd65047762f924ecd367c17eabf8f
  , amount := 0x01
  }

private def withdrawal₂ : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , recipient := 0x000f3df6d732807ef1319fb7b8bb8522d0beac02
  , amount := 0x01
  }

private def withdrawal₃ : Withdrawal :=
  { index := 0x01
  , validatorIndex := 0x01
  , recipient := 0xfffffffffffffffffffffffffffffffffffffffe
  , amount := 0x01
  }

private def withdrawalZeroTrailingRoot : Withdrawal :=
  { index := 0x00
  , validatorIndex := 0x00
  , recipient := 0x0000000000000000000000000000000000000001
  , amount := 0x00
  }

private example :
  (computeTrieRoot []).toOption
    ==
  (ByteArray.ofBlob
    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
  ).toOption
:= by native_decide

/- From newly_created_contract.json -/
private example :
  (computeTrieRoot [withdrawal₁]).toOption
    =
  (ByteArray.ofBlob
    "82cc6fbe74c41496b382fcdf25216c5af7bdbb5a3929e8f2e61bd6445ab66436"
  ).toOption
:= by native_decide

/- From beacon_root_contract_deploy.json -/
private example :
  (computeTrieRoot [withdrawal₂, withdrawal₃]).toOption
    =
  (ByteArray.ofBlob
    "2aef4d3e6939af0b4bf4c0e7572a214eb7db9ba52937e1e82ad6c64b52d2e8bb"
  ).toOption
:= by native_decide

/- From withdrawing_to_precompiles.json -/
private example :
  (computeTrieRoot [withdrawalZeroTrailingRoot]).toOption
    =
  (ByteArray.ofBlob
    "04cc2e3f94b587ff46b5f4c0787c589db306b7209f7f212f47022a12bc3e6e16"
  ).toOption
:= by native_decide
