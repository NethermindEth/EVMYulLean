import EvmYul.EVM.State

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
  | DataGreaterThan9152 : InvalidTransactionException
  | SenderRecoverError : String → InvalidTransactionException

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
      | .DataGreaterThan9152  => "DataGreaterThan9152"
      | .SenderRecoverError s => "SenderRecoverError: " ++ s

inductive Exception where
  | InvalidStackSizeException         : Exception
  | InvalidPC                         : Exception
  | OutOfBounds                       : Exception
  | NotEncodableRLP                   : Exception
  | InvalidInstruction                : Exception
  | SenderMustExist                   : Exception
  | ReceiverMustExistWithNonZeroValue : Exception
  | Underflow                         : Exception
  | Overflow                          : Exception
  | StopInvoked (s : EVM.State)       : Exception
  | OutOfFuel                         : Exception
  | InvalidTransaction :
          InvalidTransactionException → Exception

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
                    | .StopInvoked _                     => "Execution halted by STOP."
                    | .OutOfFuel                         => "OutOfFuel"
                    | .InvalidTransaction e              => "InvalidTransaction: " ++ repr e

end EVM

end EvmYul
