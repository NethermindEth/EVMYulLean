import EvmYul.EVM.State

namespace EvmYul

namespace EVM

-- TODO - fix / cleanup.
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
  | ReceiverNotInAccounts (a : Address) : Exception
  | BogusExceptionToBeReplaced (s : String) : Exception

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
                    | .ReceiverNotInAccounts (a : Address) => s!"ReceiverNotInAccounts: {a}"
                    | .BogusExceptionToBeReplaced s      => s!"BogusExceptionToBeReplaced: {s}"

end EVM

end EvmYul
