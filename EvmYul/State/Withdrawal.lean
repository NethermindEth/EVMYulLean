import EvmYul.Wheels
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

private def someWithdrawal : Withdrawal :=
  { index := 0
  , validatorIndex := 1
  , recipient := 0x00000000219ab540356cbb839cbe05303d7705fa
  , amount := 2
  }

#eval RLP someWithdrawal.to𝕋 |>.map ByteArray.data

example :
  (RLP someWithdrawal.to𝕋).map ByteArray.data
    =
  some #[216, 128, 1, 148, 0, 0, 0, 0, 33, 154, 181, 64, 53, 108, 187, 131, 156, 190, 5, 48, 61, 119, 5, 250, 2]
:= by native_decide
