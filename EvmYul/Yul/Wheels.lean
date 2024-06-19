import Mathlib.Data.Finmap

import EvmYul.Wheels

namespace EvmYul

namespace Yul

abbrev VarStore := Finmap (λ _ : Identifier ↦ Literal)

end Yul

end EvmYul
