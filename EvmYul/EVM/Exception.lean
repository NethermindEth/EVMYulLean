import EvmYul.EVM.State

namespace EvmYul

namespace EVM

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

end EVM

end EvmYul
