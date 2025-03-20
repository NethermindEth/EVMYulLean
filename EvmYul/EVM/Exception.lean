import EvmYul.Wheels
import EvmYul.Maps.AccountMap
namespace EvmYul

namespace EVM

inductive ExecutionException where
  | OutOfFuel
  | InvalidInstruction
  | OutOfGass
  | BadJumpDestination
  | StackOverflow
  | StackUnderflow
  | InvalidMemoryAccess
  | StaticModeViolation
deriving BEq

instance : Repr ExecutionException where
  reprPrec s _ :=
    match s with
      | .OutOfFuel => "OutOfFuel"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfGass => "OutOfGass"
      | .BadJumpDestination => "BadJumpDestination"
      | .StackOverflow => "StackOverflow"
      | .StackUnderflow => "StackUnderflow"
      | .InvalidMemoryAccess => "InvalidMemoryAccess"
      | .StaticModeViolation => "StaticModeViolation"

inductive BlockException where
  | INCORRECT_EXCESS_BLOB_GAS
  | INCORRECT_BLOB_GAS_USED
  | INCORRECT_BLOCK_FORMAT -- No "Cancun" test needs this
  | BLOB_GAS_USED_ABOVE_LIMIT
  | INVALID_WITHDRAWALS_ROOT
  | IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS
  | RLP_STRUCTURES_ENCODING
  | IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
  | RLP_INVALID_FIELD_OVERFLOW_64
  | RLP_INVALID_ADDRESS
  | GASLIMIT_TOO_BIG
  | INVALID_GAS_USED
  | UNKNOWN_PARENT_ZERO
  | EXTRA_DATA_TOO_BIG
  | INVALID_BLOCK_NUMBER
  | INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
  | INVALID_GASLIMIT
  | INVALID_BASEFEE_PER_GAS
  | UNKNOWN_PARENT
  | INVALID_STATE_ROOT
  | INVALID_LOG_BLOOM
  | INVALID_TRANSACTIONS_ROOT
  | INVALID_RECEIPTS_ROOT

instance : Repr BlockException where
  reprPrec s _ :=
    match s with
      | .INCORRECT_EXCESS_BLOB_GAS => "INCORRECT_EXCESS_BLOB_GAS"
      | .INCORRECT_BLOB_GAS_USED => "INCORRECT_BLOB_GAS_USED"
      | .INCORRECT_BLOCK_FORMAT => "INCORRECT_BLOCK_FORMAT"
      | .BLOB_GAS_USED_ABOVE_LIMIT => "BLOB_GAS_USED_ABOVE_LIMIT"
      | .INVALID_WITHDRAWALS_ROOT => "INVALID_WITHDRAWALS_ROOT"
      | .IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS => "IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS"
      | .RLP_STRUCTURES_ENCODING => "RLP_STRUCTURES_ENCODING"
      | .IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS => "IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS"
      | .RLP_INVALID_FIELD_OVERFLOW_64 => "RLP_INVALID_FIELD_OVERFLOW_64"
      | .RLP_INVALID_ADDRESS => "RLP_INVALID_ADDRESS"
      | .GASLIMIT_TOO_BIG => "GASLIMIT_TOO_BIG"
      | .INVALID_GAS_USED => "INVALID_GAS_USED"
      | .UNKNOWN_PARENT_ZERO => "UNKNOWN_PARENT_ZERO"
      | .EXTRA_DATA_TOO_BIG => "EXTRA_DATA_TOO_BIG"
      | .INVALID_BLOCK_NUMBER => "INVALID_BLOCK_NUMBER"
      | .INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT => "INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT"
      | .INVALID_GASLIMIT => "INVALID_GASLIMIT"
      | .INVALID_BASEFEE_PER_GAS => "INVALID_BASEFEE_PER_GAS"
      | .UNKNOWN_PARENT => "UNKNOWN_PARENT"
      | .INVALID_STATE_ROOT => "INVALID_STATE_ROOT"
      | .INVALID_LOG_BLOOM => "INVALID_LOG_BLOOM"
      | .INVALID_TRANSACTIONS_ROOT => "INVALID_TRANSACTIONS_ROOT"
      | .INVALID_RECEIPTS_ROOT => "INVALID_RECEIPTS_ROOT"

inductive TransactionException where
  | IllFormedRLP
  | INVALID_SIGNATURE_VRS
  | NONCE_MISMATCH_TOO_LOW
  | NONCE_MISMATCH_TOO_HIGH
  | SENDER_NOT_EOA
  | INSUFFICIENT_ACCOUNT_FUNDS
  | PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
  | TYPE_3_TX_ZERO_BLOBS
  | INTRINSIC_GAS_TOO_LOW
  | INSUFFICIENT_MAX_FEE_PER_BLOB_GAS
  | INITCODE_SIZE_EXCEEDED
  | NONCE_IS_MAX
  | TYPE_3_TX_BLOB_COUNT_EXCEEDED
  | GAS_ALLOWANCE_EXCEEDED
  | TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
  | INSUFFICIENT_MAX_FEE_PER_GAS
  | TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
  | TYPE_3_TX_CONTRACT_CREATION
  | GASLIMIT_PRICE_PRODUCT_OVERFLOW
  | RLP_INVALID_VALUE

/--
  TYPE_NOT_SUPPORTED - No "Cancun" test needs this
-/
instance : Repr TransactionException where
  reprPrec s _ :=
    match s with
      | .IllFormedRLP         => "IllFormedRLP"
      | .INVALID_SIGNATURE_VRS     => "INVALID_SIGNATURE_VRS"
      | .NONCE_MISMATCH_TOO_LOW   => "NONCE_MISMATCH_TOO_LOW"
      | .NONCE_MISMATCH_TOO_HIGH   => "NONCE_MISMATCH_TOO_HIGH"
      | .SENDER_NOT_EOA   => "SENDER_NOT_EOA"
      | .INSUFFICIENT_ACCOUNT_FUNDS => "INSUFFICIENT_ACCOUNT_FUNDS"
      | .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS     => "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS"
      | .TYPE_3_TX_ZERO_BLOBS => "TYPE_3_TX_ZERO_BLOBS"
      | .INTRINSIC_GAS_TOO_LOW => "INTRINSIC_GAS_TOO_LOW"
      | .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS => "INSUFFICIENT_MAX_FEE_PER_BLOB_GAS"
      | .INITCODE_SIZE_EXCEEDED => "INITCODE_SIZE_EXCEEDED"
      -- | .MAX_CODE_SIZE_EXCEEDED => "MAX_CODE_SIZE_EXCEEDED"
      | .NONCE_IS_MAX => "NONCE_IS_MAX"
      | .TYPE_3_TX_BLOB_COUNT_EXCEEDED => "TYPE_3_TX_BLOB_COUNT_EXCEEDED"
      | .GAS_ALLOWANCE_EXCEEDED => "GAS_ALLOWANCE_EXCEEDED"
      | .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED => "TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"
      | .INSUFFICIENT_MAX_FEE_PER_GAS => "INSUFFICIENT_MAX_FEE_PER_GAS"
      | .TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH => "TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH"
      | .TYPE_3_TX_CONTRACT_CREATION => "TYPE_3_TX_CONTRACT_CREATION"
      | .GASLIMIT_PRICE_PRODUCT_OVERFLOW => "GASLIMIT_PRICE_PRODUCT_OVERFLOW"
      | .RLP_INVALID_VALUE => "RLP_INVALID_VALUE"

inductive Exception where
  | ExecutionException :     ExecutionException → Exception
  | NotEncodableRLP :                             Exception
  | TransactionException : TransactionException → Exception
  | SenderRecoverError :                 String → Exception
  | BlockException :             BlockException → Exception
  | MissedExpectedException :       List String → Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .ExecutionException ee =>       "Execution exception: " ++ repr ee
      | .NotEncodableRLP =>             "NotEncodableRLP"
      | .TransactionException e =>      "TransactionException." ++ repr e
      | .SenderRecoverError s =>        "SenderRecoverError." ++ s
      | .BlockException be =>           "BlockException." ++ repr be
      | .MissedExpectedException mee =>
        "Missed expected exception: " ++ String.intercalate "|" mee

end EVM

end EvmYul
