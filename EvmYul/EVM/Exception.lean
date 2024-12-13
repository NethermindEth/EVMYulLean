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
  -- | CALL_DEPTH_EXCEEDED
  | InvalidMemoryAccess
  | StaticModeViolation
  -- | PRECOMPILE_FAILURE
  -- | NONCE_EXCEEDED

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
  | INCORRECT_BLOCK_FORMAT -- TODO: No "Cancun" test needs this
  | BLOB_GAS_USED_ABOVE_LIMIT
  | INVALID_WITHDRAWALS_ROOT

instance : Repr BlockException where
  reprPrec s _ :=
    match s with
      | .INCORRECT_EXCESS_BLOB_GAS => "INCORRECT_EXCESS_BLOB_GAS"
      | .INCORRECT_BLOB_GAS_USED => "INCORRECT_BLOB_GAS_USED"
      | .INCORRECT_BLOCK_FORMAT => "INCORRECT_BLOCK_FORMAT"
      | .BLOB_GAS_USED_ABOVE_LIMIT => "BLOB_GAS_USED_ABOVE_LIMIT"
      | .INVALID_WITHDRAWALS_ROOT => "INVALID_WITHDRAWALS_ROOT"

inductive TransactionException where
  | IllFormedRLP
  | InvalidSignature
  | NONCE_MISMATCH_TOO_LOW
  | NONCE_MISMATCH_TOO_HIGH
  | SENDER_NOT_EOA
  | INSUFFICIENT_ACCOUNT_FUNDS
  | BaseFeeTooHigh
  | InconsistentFees
  | TYPE_3_TX_ZERO_BLOBS
  | TYPE_3_TX_PRE_FORK -- TODO: No "Cancun" test needs this
  | INTRINSIC_GAS_TOO_LOW
  | INSUFFICIENT_MAX_FEE_PER_BLOB_GAS
  | INITCODE_SIZE_EXCEEDED
  | MAX_CODE_SIZE_EXCEEDED
  | NONCE_IS_MAX
  | TYPE_3_TX_BLOB_COUNT_EXCEEDED
  | GAS_ALLOWANCE_EXCEEDED -- TODO: What is this

instance : Repr TransactionException where
  reprPrec s _ :=
    match s with
      | .IllFormedRLP         => "IllFormedRLP"
      | .InvalidSignature     => "InvalidSignature"
      | .NONCE_MISMATCH_TOO_LOW   => "NONCE_MISMATCH_TOO_LOW"
      | .NONCE_MISMATCH_TOO_HIGH   => "NONCE_MISMATCH_TOO_HIGH"
      | .SENDER_NOT_EOA   => "SENDER_NOT_EOA"
      | .INSUFFICIENT_ACCOUNT_FUNDS => "INSUFFICIENT_ACCOUNT_FUNDS"
      | .BaseFeeTooHigh       => "BaseFeeTooHigh"
      | .InconsistentFees     => "InconsistentFees"
      | .TYPE_3_TX_ZERO_BLOBS => "TYPE_3_TX_ZERO_BLOBS"
      | .TYPE_3_TX_PRE_FORK => "TYPE_3_TX_PRE_FORK"
      | .INTRINSIC_GAS_TOO_LOW => "INTRINSIC_GAS_TOO_LOW"
      | .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS => "INSUFFICIENT_MAX_FEE_PER_BLOB_GAS"
      | .INITCODE_SIZE_EXCEEDED => "INITCODE_SIZE_EXCEEDED"
      | .MAX_CODE_SIZE_EXCEEDED => "MAX_CODE_SIZE_EXCEEDED"
      | .NONCE_IS_MAX => "NONCE_IS_MAX"
      | .TYPE_3_TX_BLOB_COUNT_EXCEEDED => "TYPE_3_TX_BLOB_COUNT_EXCEEDED"
      | .GAS_ALLOWANCE_EXCEEDED => "GAS_ALLOWANCE_EXCEEDED"

-- TODO - fix / cleanup.
inductive Exception where
  -- | OutOfFuel :                                   Exception
  -- | InvalidInstruction :                          Exception
  -- | OutOfGass :                                   Exception
  -- | BadJumpDestination :                          Exception
  -- | StackOverflow :                               Exception
  -- | StackUnderflow :                              Exception
  -- | InvalidMemoryAccess :                         Exception
  -- | StaticModeViolation :                         Exception
  | ExecutionException :     ExecutionException → Exception
  -- | InvalidPC                                   : Exception
  -- | OutOfBounds                                 : Exception
  | NotEncodableRLP :                             Exception
  -- | SenderMustExist                             : Exception
  -- | ReceiverMustExistWithNonZeroValue           : Exception
  -- | Underflow                                   : Exception
  -- | Overflow                                    : Exception
  -- | StopInvoked (s : EVM.State)                 : Exception
  | TransactionException : TransactionException → Exception
  -- | ReceiverNotInAccounts (a : AccountAddress)  : Exception
  -- | InvalidWithdrawal (s : String) : Exception
  -- | BogusExceptionToBeReplaced (s : String) : Exception
  -- | ExpectedException (post : AccountMap)   : Exception
  | SenderRecoverError :                 String → Exception
  | BlockException :             BlockException → Exception
  | MissedExpectedException :            String → Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .ExecutionException ee =>       "Execution exception: " ++ repr ee
      -- | .StaticModeViolation =>         "StaticModeViolation"
      -- | .BadJumpDestination =>          "BadJumpDestination"
      -- | .InvalidMemoryAccess =>         "InvalidMemoryAccess"
      -- | .StackUnderflow =>              "StackUnderflow"
      -- | .StackOverflow =>               "StackOverflow"
      -- | .InvalidPC                         => "InvalidPC"
      -- | .OutOfBounds                       => "OutOfBounds"
      | .NotEncodableRLP =>             "NotEncodableRLP"
      -- | .InvalidInstruction =>          "InvalidInstruction"
      -- | .SenderMustExist                   => "SenderMustExist"
      -- | .ReceiverMustExistWithNonZeroValue => "ReceiverMustExistWithNonZeroValue"
      -- | .Underflow                         => "Underflow"
      -- | .Overflow                          => "Overflow"
      -- | .StopInvoked _                     => "Execution halted by STOP."
      -- | .OutOfFuel =>                   "OutOfFuel"
      -- | .OutOfGass =>                   "OutOfGass"
      | .TransactionException e =>      "TransactionException." ++ repr e
      -- | .ReceiverNotInAccounts
      --     (a : AccountAddress)             => s!"ReceiverNotInAccounts: {a}"
      -- | .InvalidWithdrawal s               => s!"InvalidWithdrawal: {s}"
      -- | .BogusExceptionToBeReplaced s      => s!"BogusExceptionToBeReplaced: {s}"
      -- | .ExpectedException _               => s!"Expected exception"
      | .SenderRecoverError s =>        "SenderRecoverError." ++ s
      | .BlockException be =>           "BlockException." ++ repr be
      | .MissedExpectedException mee => "Missed expected exception" ++ mee

#eval repr (Exception.BlockException .INCORRECT_EXCESS_BLOB_GAS)

end EVM

end EvmYul
