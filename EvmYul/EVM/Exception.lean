import EvmYul.Wheels

namespace EvmYul

namespace EVM

inductive InvalidTransactionException where
  | IllFormedRLP : InvalidTransactionException
  | InvalidSignature : InvalidTransactionException
  | InvalidSenderNonce : InvalidTransactionException
  | SenderCodeNotEmpty : InvalidTransactionException
  | UpFrontPayment : InvalidTransactionException
  | BaseFeeTooHigh : InvalidTransactionException
  | InconsistentFees : InvalidTransactionException
  | InitCodeDataGreaterThan49152 : InvalidTransactionException
  | TYPE_3_TX_ZERO_BLOBS : InvalidTransactionException
  | TYPE_3_TX_PRE_FORK : InvalidTransactionException
  | INTRINSIC_GAS_TOO_LOW : InvalidTransactionException

instance : Repr InvalidTransactionException where
  reprPrec s _ :=
    match s with
      | .IllFormedRLP         => "IllFormedRLP"
      | .InvalidSignature     => "InvalidSignature"
      | .InvalidSenderNonce   => "InvalidSenderNonce"
      | .SenderCodeNotEmpty   => "SenderCodeNotEmpty"
      | .UpFrontPayment       => "UpFrontPayment"
      | .BaseFeeTooHigh       => "BaseFeeTooHigh"
      | .InconsistentFees     => "InconsistentFees"
      | .InitCodeDataGreaterThan49152  => "InitCodeDataGreaterThan49152"
      | .TYPE_3_TX_ZERO_BLOBS => "TYPE_3_TX_ZERO_BLOBS"
      | .TYPE_3_TX_PRE_FORK => "TYPE_3_TX_PRE_FORK"
      | .INTRINSIC_GAS_TOO_LOW => "INTRINSIC_GAS_TOO_LOW"

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
  | InvalidTransaction :
                    InvalidTransactionException → Exception
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
                    | .InvalidTransaction e              => "InvalidTransaction: " ++ repr e
                    | .ReceiverNotInAccounts
                        (a : AccountAddress)             => s!"ReceiverNotInAccounts: {a}"
                    | .InvalidWithdrawal s               => s!"InvalidWithdrawal: {s}"
                    | .BogusExceptionToBeReplaced s      => s!"BogusExceptionToBeReplaced: {s}"
                    | .ExpectedException s               => s!"Expected exception: {s}"
                    | .SenderRecoverError s              => "SenderRecoverError: " ++ s
                    | .BlockException_INCORRECT_EXCESS_BLOB_GAS => "BlockException_INCORRECT_EXCESS_BLOB_GAS"
                    | .BlockException_INCORRECT_BLOB_GAS_USED => "BlockException_INCORRECT_BLOB_GAS_USED"
                    | .BlockException_INCORRECT_BLOCK_FORMAT => "BlockException_INCORRECT_BLOCK_FORMAT"

end EVM

end EvmYul
