This repository contains a formal model of the EVM and Yul in Lean 4.
Where applicable, the underlying EVM primops are used directly by the Yul model.

Everything here is work in progress and is subject to change therefore.

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
EvmYul/Operations.lean
```

The semantic function `primCall` associated with the ADT:
```
EvmYul/Yul/PrimOps.lean
```

## EVM
The model of the EVM state `EVM.State`:
```
EvmYul/EVM/State.lean
```

The semantic function `step`:
```
EvmYul/EVM/Semantics.lean
```

## Yul
The ADT `Stmt` mutually defined with `Expr` and `FunctionDefinition` describing Yul:
```
EvmYul/Yul/Ast.lean
```

The model of the Yul state `YUL.State`:
```
EvmYul/Yul/State.lean
```

The semantic function `exec` mutually defined with `eval` (and some misc. functions):
```
EvmYul/Yul/Interpreter.lean
```
