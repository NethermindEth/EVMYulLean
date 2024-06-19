import EvmYul.EVM.Exception

namespace EvmYul

namespace Conform

/--
`Exception` represents the class of conformance testing errors.
- `CannotParse`          - The `Json` of a test is malformed. `why` is the reason. 
- `EVMError`             - There was an EVM `exc` error running code associated with `addr`.
- `InvalidTestStructure` - The structure of tests has been violated. `why` is the reason. 
- `TestFailed`           - The postState associated with `addr` differs from the state we arrived at
                           by executing the model of the EVM starting in the state obtained from 
                           pre associated with `addr`.
-/
inductive Exception :=
  | CannotParse (why : String)
  | EVMError (exc : EVM.Exception)
  | InvalidTestStructure (why : String)
  deriving Repr
end Conform

end EvmYul
