/-
Human-eyeball friendly version of various data used throughout the project.
Mostly used for debugging, possibly for reporting.

The function for pretty printing is always `<Datatype>.pretty (self : Datatype) : String`
modulo parametricity.
-/

import EvmYul.Operations

import Conform.Wheels

namespace EvmYul

/--
Strip the existing `repr` a'la:
- EvmYul.Operation.Push (EvmYul.Operation.POp.PUSH1) → PUSH1

This breaks the moment that `Repr` changes its behaviour; it is fine for the time being.
-/
def Operation.pretty (self : Operation .EVM) : String :=
  let reprStr := ToString.toString <| repr self
  let lastComponent := reprStr.splitOn "." |>.getLast!
  lastComponent.take lastComponent.length.pred

end EvmYul
