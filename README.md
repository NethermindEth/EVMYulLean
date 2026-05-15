This repository contains a formal model of the EVM and Yul in Lean 4.
Where applicable, the underlying EVM primops are used directly by the Yul model.

Everything here is work in progress and is subject to change therefore.

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc

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

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.

# Yul semantics tests

To execute the Yul semantics tests run:

`lake exe yulSemanticsTests`

These tests are defined in `EvmYul/Yul/YulSemanticsTests/Main.lean`.

# Limitations of the Yul semantics

## Fallback function from receiving ether

- We do not run a the fallback function of a smart contract when it receives ether, such as being a recipient of ether in a `SELFDESTRUCT` of another contract.

## Gas

- We do not model gas in the Yul semantics, no fee is deducted.

## Create

- We do not model `create` or `create2` because Yul code is not stored as bytecode, and so we cannot properly model `create` or `create2` without some mechanism for correctly decompiling bytecode into Yul code, so we do not model this.
- This case is caught by the the `_` in the match statement in `EVMYul/Semantics.lean` and returns `default`.
- Instead of creating contracts, they should be manually included in the modelled blockchain state, in the `accountMap`. See `EvmYul/Yul/YulSemanticsTests/README.md` for more information on how to include custom Solidity contracts in the modelled blockchain state.

## EXTCODESIZE

- Not modelled, the current semantics raise an error. Solidity checks `extcodesize` and so generated Yul will not be able to call other contracts without removing or editing these `extcodesize` checks (manually).
- In the `EvmYul/Yul/YulSemanticsTests.lean` we manually changed `let _1 := extcodesize( 2)` to `let _1 := 1` in `fun_testStoreAndRetrieveExternal`.

## Other contract code related opcodes not modelled
- We also do not model `EXTCODEHASH`, `EXTCODECOPY`, `CODECOPY`, `CODESIZE` for similar reasons to not modelling `EXTCODESIZE`.
- These cases are caught by the the `_` in the match statement in `EVMYul/Semantics.lean` and return `default`.

## SELFDESTRUCT

- Yul `SELFDESTRUCT` halts execution after applying the modelled account and substate effects. The semantics for `SELFDESTRUCT` still have limitations, such as not triggering the fallback function in a contract that is the recipient of the ether from the contract the self-destructs. We may remove the semantics for `SELFDESTRUCT` once its status changes from deprecated to not being supported.
