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
  | CannotParse (why : String)
  -- | EVMError (exc : EVM.Exception)
  | InvalidTestStructure (why : String)
  deriving Repr

-- def Exception.toFilePath : Exception → System.FilePath
--   | .CannotParse f _ _ | .InvalidTestStructure f _ _ => f

-- def Exception.toTest : Exception → String
--   | .CannotParse _ t _ | .InvalidTestStructure _ t _ => t

end Conform

end EvmYul
