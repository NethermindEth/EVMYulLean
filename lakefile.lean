import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.16.0-rc2"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`DautoImplicit, false⟩]
}

@[default_target]
lean_lib «EvmYul»

lean_lib «Conform»

lean_exe «conform» where
  root := `Conform.Main
