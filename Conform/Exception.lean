import EvmYul.EVM.Exception

namespace EvmYul

namespace Conform

/--
`Exception` represents the class of conformance testing errors.
- `CannotParse`          - The `Json` of a test is malformed. `why` is the reason. 
- `EVMError`             - There was an EVM `exc` error running code associated with `addr`.
- `InvalidTestStructure` - The structure of tests has been violated. `why` is the reason. 
-/
inductive Exception :=
  | CannotParse (file : System.FilePath) (why : String)
  -- | EVMError (exc : EVM.Exception)
  | InvalidTestStructure (file : System.FilePath) (why : String)
  deriving Repr

def Exception.toFilePath : Exception → System.FilePath
  | .CannotParse f _ | .InvalidTestStructure f _ => f

end Conform

end EvmYul
