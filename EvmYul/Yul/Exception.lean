import EvmYul.Yul.State

namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments                              : Exception
  | NotEncodableRLP                               : Exception
  | InvalidInstruction                            : Exception
  | OutOfFuel                                     : Exception
  | StaticModeViolation                           : Exception
  | MissingContract (s : String)                  : Exception
  | MissingContractFunction (s : String)          : Exception
  | InvalidExpression                             : Exception
  | UnknownIdentifier (s : String)                : Exception
  | DuplicateDeclaration (s : String)             : Exception
  | YulEXTCODESIZENotImplemented                  : Exception
  | Revert (state : Yul.State)                    : Exception
  | YulHalt (state : Yul.State) (value : UInt256) : Exception
  -- | StopInvoked        : Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .InvalidArguments => "InvalidArguments"
      | .NotEncodableRLP => "NotEncodableRLP"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfFuel => "OutOfFuel"
      | .StaticModeViolation => "StaticModeViolation"
      | .MissingContract s => "MissingContract: " ++ s
      | .MissingContractFunction f => "MissingContractFunction: " ++ f
      | .InvalidExpression => "InvalidExpression"
      | .UnknownIdentifier s => "UnknownIdentifier: " ++ s
      | .DuplicateDeclaration s => "DuplicateDeclaration: " ++ s
      | .YulEXTCODESIZENotImplemented => "YulEXTCODESIZENotImplemented"
      | .Revert _ => "Revert"
      | .YulHalt _ _ => "YulHalt: (holds a state and a value)"


end Yul

end EvmYul
