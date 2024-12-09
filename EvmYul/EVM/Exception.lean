import EvmYul.Wheels

namespace EvmYul

namespace EVM

inductive TransactionExceptionException where
  | IllFormedRLP : TransactionExceptionException
  | InvalidSignature : TransactionExceptionException
  | InvalidSenderNonce : TransactionExceptionException
  | SenderCodeNotEmpty : TransactionExceptionException
  | INSUFFICIENT_ACCOUNT_FUNDS : TransactionExceptionException
  | BaseFeeTooHigh : TransactionExceptionException
  | InconsistentFees : TransactionExceptionException
  | InitCodeDataGreaterThan49152 : TransactionExceptionException
  | TYPE_3_TX_ZERO_BLOBS : TransactionExceptionException
  | TYPE_3_TX_PRE_FORK : TransactionExceptionException
  | INTRINSIC_GAS_TOO_LOW : TransactionExceptionException
  | INSUFFICIENT_MAX_FEE_PER_BLOB_GAS : TransactionExceptionException
  | INITCODE_SIZE_EXCEEDED : TransactionExceptionException
  | MAX_CODE_SIZE_EXCEEDED : TransactionExceptionException
  | NONCE_IS_MAX : TransactionExceptionException

instance : Repr TransactionExceptionException where
  reprPrec s _ :=
    match s with
      | .IllFormedRLP         => "IllFormedRLP"
      | .InvalidSignature     => "InvalidSignature"
      | .InvalidSenderNonce   => "InvalidSenderNonce"
      | .SenderCodeNotEmpty   => "SenderCodeNotEmpty"
      | .INSUFFICIENT_ACCOUNT_FUNDS => "INSUFFICIENT_ACCOUNT_FUNDS"
      | .BaseFeeTooHigh       => "BaseFeeTooHigh"
      | .InconsistentFees     => "InconsistentFees"
      | .InitCodeDataGreaterThan49152  => "InitCodeDataGreaterThan49152"
      | .TYPE_3_TX_ZERO_BLOBS => "TYPE_3_TX_ZERO_BLOBS"
      | .TYPE_3_TX_PRE_FORK => "TYPE_3_TX_PRE_FORK"
      | .INTRINSIC_GAS_TOO_LOW => "INTRINSIC_GAS_TOO_LOW"
      | .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS => "INTRINSIC_GAS_TOO_LOW"
      | .INITCODE_SIZE_EXCEEDED => "INITCODE_SIZE_EXCEEDED"
      | .MAX_CODE_SIZE_EXCEEDED => "MAX_CODE_SIZE_EXCEEDED"
      | .NONCE_IS_MAX => "NONCE_IS_MAX"

-- TODO - fix / cleanup.
inductive Exception where
  | InvalidStackSizeException                   : Exception
  | InvalidPC                                   : Exception
  | OutOfBounds                                 : Exception
  | NotEncodableRLP                             : Exception
  | InvalidInstruction                          : Exception
  | SenderMustExist                             : Exception
  | ReceiverMustExistWithNonZeroValue           : Exception
  | Underflow                                   : Exception
  | Overflow                                    : Exception
  -- | StopInvoked (s : EVM.State)                 : Exception
  | OutOfFuel                                   : Exception
  | OutOfGass                                   : Exception
  | TransactionException :
                    TransactionExceptionException → Exception
  | ReceiverNotInAccounts (a : AccountAddress)  : Exception
  | InvalidWithdrawal (s : String) : Exception
  | BogusExceptionToBeReplaced (s : String) : Exception
  | ExpectedException (s : String)          : Exception
  | SenderRecoverError             : String → Exception
  | BlockException_INCORRECT_EXCESS_BLOB_GAS : Exception
  | BlockException_INCORRECT_BLOB_GAS_USED : Exception
  | BlockException_INCORRECT_BLOCK_FORMAT

instance : Repr Exception where
  reprPrec s _ := match s with
                    | .InvalidStackSizeException         => "InvalidStackSizeException"
                    | .InvalidPC                         => "InvalidPC"
                    | .OutOfBounds                       => "OutOfBounds"
                    | .NotEncodableRLP                   => "NotEncodableRLP"
                    | .InvalidInstruction                => "InvalidInstruction"
                    | .SenderMustExist                   => "SenderMustExist"
                    | .ReceiverMustExistWithNonZeroValue => "ReceiverMustExistWithNonZeroValue"
                    | .Underflow                         => "Underflow"
                    | .Overflow                          => "Overflow"
                    -- | .StopInvoked _                     => "Execution halted by STOP."
                    | .OutOfFuel                         => "OutOfFuel"
                    | .OutOfGass                         => "OutOfGass"
                    | .TransactionException e              => "TransactionException." ++ repr e
                    | .ReceiverNotInAccounts
                        (a : AccountAddress)             => s!"ReceiverNotInAccounts: {a}"
                    | .InvalidWithdrawal s               => s!"InvalidWithdrawal: {s}"
                    | .BogusExceptionToBeReplaced s      => s!"BogusExceptionToBeReplaced: {s}"
                    | .ExpectedException s               => s!"Expected exception: {s}"
                    | .SenderRecoverError s              => "SenderRecoverError." ++ s
                    | .BlockException_INCORRECT_EXCESS_BLOB_GAS => "BlockException.INCORRECT_EXCESS_BLOB_GAS"
                    | .BlockException_INCORRECT_BLOB_GAS_USED => "BlockException.INCORRECT_BLOB_GAS_USED"
                    | .BlockException_INCORRECT_BLOCK_FORMAT => "BlockException.INCORRECT_BLOCK_FORMAT"

end EVM

end EvmYul
