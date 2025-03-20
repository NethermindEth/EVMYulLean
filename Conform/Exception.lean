import EvmYul.EVM.Exception

namespace EvmYul

namespace Conform

/--
`Exception` represents the class of conformance testing errors.
- `CannotParse`          - The `Json` of a test is malformed. `why` is the reason. 
- `InvalidTestStructure` - The structure of tests has been violated. `why` is the reason. 
-/
inductive Exception :=
  | CannotParse (why : String)
  | InvalidTestStructure (why : String)
  deriving Repr

end Conform

end EvmYul
