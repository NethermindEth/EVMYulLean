import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"f0957a7575317490107578ebaee9efaf8e62a4ab"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`DautoImplicit, false⟩]
}

@[default_target]
lean_lib «EvmYul»

lean_lib «Conform» 

lean_exe «conform» where
  root := `Conform.Main
