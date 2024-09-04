import EvmYul.UInt256
import EvmYul.MachineStateOps
import EvmYul.MachineState

import Mathlib.Data.Finmap

namespace EvmYul

set_option autoImplicit true

inductive OperationType where
  | Yul
  | EVM
  deriving DecidableEq, Repr

namespace Operation

section Operation

/--
  Stop and Arithmetic Operations
-/
inductive SAOp (τ : OperationType) : Type where
  /--
    Stop: halts program execution
    δ: 0 ; α : 0
  -/
  | protected STOP : SAOp τ
  /--
    ADD: adds two stack values.
    δ: 2 ; α : 1
  -/
  | protected ADD : SAOp τ
  /--
    MUL: multiplies two stack values.
    δ: 2 ; α : 1
  -/
  | protected MUL : SAOp τ
  /--
    SUB: subtracts two stack values.
    δ: 2 ; α : 1
  -/
  | protected SUB : SAOp τ
  /--
    DIV: divides two stack values.
    δ: 2 ; α: 1
  -/
  | protected DIV : SAOp τ
  /--
    SDIV: signed integer division
    δ: 2 ; α: 1
  -/
  | protected SDIV : SAOp τ
  /--
    MOD: Modulo remainder operation
    δ: 2 ; α: 1
  -/
  | protected MOD : SAOp τ
  /--
    SMOD: signed integer remainder
    δ: 2 ; α: 1
  -/
  | protected SMOD : SAOp τ
  /--
    ADDMOD: addition modulo operation
    δ: 3 ; α: 1
  -/
  | protected ADDMOD : SAOp τ
  /--
    MULMOD: multiplication modulo operation
    δ: 3 ; α: 1
  -/
  | protected MULMOD : SAOp τ
  /--
    EXP: Exponential operation
    δ:2 ; α: 1
  -/
  | protected EXP : SAOp τ
  /--
    SIGNEXTEND: Extend length of two's complement signed integer
    δ: 2 ; α: 1
  -/
  | protected SIGNEXTEND : SAOp τ
  deriving DecidableEq, Repr

/--
  Comparison & Bitwise Logic Operations
-/
inductive CBLOp (τ : OperationType) : Type where
  /--
    LT: less than comparison
    δ: 2 ; α: 1
  -/
  | protected LT : CBLOp τ
  /--
    GT: greater than comparison
    δ: 2 ; α: 1
  -/
  | protected GT : CBLOp τ
  /--
    SLT: signed less-than comparison
    δ:2 ; α: 1
  -/
  | protected SLT : CBLOp τ
  /--
    SGT: signed greater-than comparison
    δ: 2 ; α: 1
  -/
  | protected SGT : CBLOp τ
  /--
    EQ: equality test
    δ:2 ; α : 1
  -/
  | protected EQ : CBLOp τ
  /--
    ISZERO: simple not operation
    δ: 1 ; α : 1
  -/
  | protected ISZERO : CBLOp τ
  /--
    AND: bitwise and
    δ:2 ; α: 1
  -/
  | protected AND : CBLOp τ
  /--
    OR: bitwise or
    δ: 2 ; α: 1
  -/
  | protected OR : CBLOp τ
  /--
    XOR: bitwise xor
    δ: 2 ; α: 1
  -/
  | protected XOR : CBLOp τ
  /--
    NOT: bitwise not
    δ:1 ; α: 1
  -/
  | protected NOT : CBLOp τ
  /--
    BYTE: retrieve single byte from a word
    δ:2 ; α:1
  -/
  | protected BYTE : CBLOp τ
  /--
    SHL: shift left operation
    δ:2 ; α: 1
  -/
  | protected SHL : CBLOp τ
  /--
    SHR: logical shift right operation
    δ:2 ; α:1
  -/
  | protected SHR : CBLOp τ
  /--
    SAR: arithmetical shift right operation
    δ:2 ; α:1
  -/
  | protected SAR : CBLOp τ
  deriving DecidableEq, Repr

/--
  Keccak operation.
-/
inductive KOp : OperationType → Type where
  /--
    KECCAK256: compute KECCAK256 hash
    δ:2 ; α: 1
  -/
  | protected KECCAK256 : KOp τ
  deriving DecidableEq, Repr

/--
  Environment Information.
-/
inductive EOp : OperationType → Type where
  /--
    ADDRESS: get the address of current executing account
    δ:0 ; α: 1
  -/
  | protected ADDRESS : EOp τ
  /--
    BALANCE: get the balance of an input account
    δ:1 ; α: 1
  -/
  | protected BALANCE : EOp τ
  /--
    ORIGIN: get execution origination address
    δ:0 ; α: 1
  -/
  | protected ORIGIN : EOp τ
  /--
    CALLER: returns the caller address
    δ: 0 ; α: 1
  -/
  | protected CALLER : EOp τ
  /--
    CALLVALUE: get deposited value by the instruction / transaction
    responsible for this execution.
    δ: 0 ; α: 1
  -/
  | protected CALLVALUE : EOp τ
  /--
    CALLDATALOAD: get input data of current environment
    δ: 1 ;  α: 1
  -/
  | protected CALLDATALOAD : EOp τ
  /--
    CALLDATASIZE: get size of input data in current environment
    δ: 0 ; α: 1
  -/
  | protected CALLDATASIZE : EOp τ
  /--
    CALLDATACOPY: copy input data from environment to memory
    δ: 3 ; α: 0
  -/
  | protected CALLDATACOPY : EOp τ
  /--
    CODESIZE: get the size of code running in current environment
    δ:0 ; α: 1
  -/
  | protected GASPRICE : EOp τ
  /--
    CODECOPY: Copy code running in current environment to memory
    δ: 3 ; α: 0
  -/
  | protected CODESIZE : EOp τ
  /--
    GASPRICE: Gas price in current execution environment
    δ: 0 ; α: 1
  -/
  | protected CODECOPY : EOp τ
  /--
    EXTCODESIZE: get the size of an account's code
    δ:1 ; α: 1
  -/
  | protected EXTCODESIZE : EOp τ
  /--
    EXTCODECOPY: copy an account's code to memory
    δ: 4 ; α: 0
  -/
  | protected EXTCODECOPY : EOp τ
  /--
    RETURNDATASIZE: get the size of output data from the previous call
                    from the current environment.
    δ: 0 ; α: 1
  -/
  | protected RETURNDATASIZE : EOp τ
  /--
    RETURNDATACOPY: copy output data from previous call to memory
    δ: 3 ; α: 0
  -/
  | protected RETURNDATACOPY : EOp τ
  /--
    EXTCODEHASH: get hash of an account's code
    δ: 1 ; α: 1
  -/
  | protected EXTCODEHASH : EOp τ
  deriving DecidableEq, Repr

/--
  Block Information.
-/
inductive BOp : OperationType → Type where
  /--
    BLOCKHASH: get the hash of one of the 256 most recent blocks
    δ:1 ; α: 1
  -/
  | protected BLOCKHASH : BOp τ
  /--
    COINBASE: get current's block beneficiary address
    δ: 0 ; α: 1
  -/
  | protected COINBASE : BOp τ
  /--
    TIMESTAMP: get current block's timestamp
    δ: 0 ; α: 1
  -/
  | protected TIMESTAMP : BOp τ
  /--
    NUMBER: get current block's number
    δ: 0 ; α: 1
  -/
  | protected NUMBER : BOp τ
  | protected PREVRANDAO : BOp τ
  /--
    DIFFICULTY: get current block's difficulty
    δ: 0 ; α: 1
  -/
  | protected DIFFICULTY : BOp τ
  /--
    GASLIMIT: get the gas limit for the current block
    δ: 0 ; α: 1
  -/
  | protected GASLIMIT : BOp τ
  /--
    CHAINID: returns the chainid, β
    δ: 0 ; α: 1
  -/
  | protected CHAINID : BOp τ
  /--
    SELFBALANCE: get the balance of the current executing account
    δ: 0 ; α: 1
  -/
  | protected SELFBALANCE : BOp τ
  | protected BASEFEE : BOp τ
  deriving DecidableEq, Repr

/--
  Stack, Memory, Storage and Flow Operations
-/
inductive SMSFOp : OperationType → Type where
  /--
    POP: remove an item from the stack
    δ: 1 ; α: 0
  -/
  | protected POP : SMSFOp τ
  /--
    MLOAD: load word from memory
    δ: 1 ; α: 1
  -/
  | protected MLOAD : SMSFOp τ
  /--
    MSTORE: save word in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE : SMSFOp τ
  /--
    SLOAD: load word from storage
    δ: 1 ; α: 1
  -/
  | protected SLOAD : SMSFOp τ
  /--
    SSTORE: Save word to storage
    δ:2 ; α: 0
  -/
  | protected SSTORE : SMSFOp τ
  /--
    MSTORE8: save byte in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE8 : SMSFOp τ
  /--
    JUMP: modify program counter
    δ:1 ; α: 0
  -/
  | protected JUMP : SMSFOp .EVM
  /--
    JUMPI: conditionally modify program counter
    δ: 2 ; α: 0
  -/
  | protected JUMPI : SMSFOp .EVM
  /--
    PC: get program counter before increment
    δ: 0 ; α: 1
  -/
  | protected PC : SMSFOp .EVM
  /--
    MSIZE: get the size of active memory in bytes
    δ: 0 ; α: 1
  -/
  | protected MSIZE : SMSFOp τ
  /--
    GAS: get the amount of available gas
    δ: 0 ; α: 1
  -/
  | protected GAS : SMSFOp τ
  /--
    JUMPDEST: mark a valid destination for jumps
    δ: 0 ; α: 0
  -/
  | protected JUMPDEST : SMSFOp .EVM
  /--
    EIP-1153
    TLOAD: load word from transient memory
    δ: 1 ; α: 1
  -/
  | protected TLOAD : SMSFOp τ
  /--
    EIP-1153
    TSTORE: Save word to transient memory
    δ: 2 ; α: 0
  -/
  | protected TSTORE : SMSFOp τ
  /--
    EIPS-5656
    MCOPY: copy memory areas
    δ: 3 ; α: 0
  -/
  | protected MCOPY : SMSFOp τ  deriving DecidableEq, Repr

/--
  Push operations.

  PUSH0 : pushes `0` to stack.
    δ: 0 ; α: 1

  PUSHn : pushes n bytes to stack.
    δ: 0 ; α: 1
-/
inductive POp : Type where
  | protected PUSH0 : POp
  | protected PUSH1 : POp
  | protected PUSH2 : POp
  | protected PUSH3 : POp
  | protected PUSH4 : POp
  | protected PUSH5 : POp
  | protected PUSH6 : POp
  | protected PUSH7 : POp
  | protected PUSH8 : POp
  | protected PUSH9 : POp
  | protected PUSH10 : POp
  | protected PUSH11 : POp
  | protected PUSH12 : POp
  | protected PUSH13 : POp
  | protected PUSH14 : POp
  | protected PUSH15 : POp
  | protected PUSH16 : POp
  | protected PUSH17 : POp
  | protected PUSH18 : POp
  | protected PUSH19 : POp
  | protected PUSH20 : POp
  | protected PUSH21 : POp
  | protected PUSH22 : POp
  | protected PUSH23 : POp
  | protected PUSH24 : POp
  | protected PUSH25 : POp
  | protected PUSH26 : POp
  | protected PUSH27 : POp
  | protected PUSH28 : POp
  | protected PUSH29 : POp
  | protected PUSH30 : POp
  | protected PUSH31 : POp
  | protected PUSH32 : POp
  deriving DecidableEq, Repr

/--
  Duplicate Operations.

  DUPn: duplicates the nth item on the stack.
    δ: n ; α: n + 1
-/
inductive DOp : Type where
  | protected DUP1
  | protected DUP2
  | protected DUP3
  | protected DUP4
  | protected DUP5
  | protected DUP6
  | protected DUP7
  | protected DUP8
  | protected DUP9
  | protected DUP10
  | protected DUP11
  | protected DUP12
  | protected DUP13
  | protected DUP14
  | protected DUP15
  | protected DUP16
  deriving DecidableEq, Repr

/--
  Exchange Operations.

  SWAPn: swaps the 1st and nth element of the stack.
    δ: n + 1 ; α: n + 1

-/
inductive ExOp : Type where
  | protected SWAP1  : ExOp
  | protected SWAP2  : ExOp
  | protected SWAP3  : ExOp
  | protected SWAP4  : ExOp
  | protected SWAP5  : ExOp
  | protected SWAP6  : ExOp
  | protected SWAP7  : ExOp
  | protected SWAP8  : ExOp
  | protected SWAP9  : ExOp
  | protected SWAP10 : ExOp
  | protected SWAP11 : ExOp
  | protected SWAP12 : ExOp
  | protected SWAP13 : ExOp
  | protected SWAP14 : ExOp
  | protected SWAP15 : ExOp
  | protected SWAP16 : ExOp
  deriving DecidableEq, Repr

/--
  Logging Operations.

  LOGn: append log record with n topics.
    δ: n + 2 ; α : 0
-/
inductive LOp : OperationType → Type where
  | protected LOG0 : LOp τ
  | protected LOG1 : LOp τ
  | protected LOG2 : LOp τ
  | protected LOG3 : LOp τ
  | protected LOG4 : LOp τ
  deriving DecidableEq, Repr

/--
  System Operations.
-/
inductive SOp : OperationType → Type where
  /--
    CREATE: create a new account with associated code
    δ: 3 ; α: 1
  -/
  | protected CREATE : SOp τ
  /--
    CALL: message call into an account
    δ: 7 ; α: 1
  -/
  | protected CALL : SOp τ
  /--
    CALLCODE: message call into this account with an alternative account's code
    δ: 7 ; α: 1
  -/
  | protected CALLCODE : SOp τ
  /--
    RETURN: Halt execution returning output data
    δ: 2 ; α: 0
  -/
  | protected RETURN : SOp τ
  /--
    DELEGATECALL: message call into this account with an alternative account's code
                  but persisting the current values for sender and value
    δ: 6 ; α: 1
  -/
  | protected DELEGATECALL : SOp τ
  /--
    CREATE2: create a new account with associated code
    δ: 4 ; α: 1
  -/
  | protected CREATE2 : SOp τ
  /--
    STATICCALL: static message call into an account
    δ: 6 ; α: 1
  -/
  | protected STATICCALL : SOp τ
  /--
    REVERT: halt execution reverting state changes but returning data and remaining gas
    δ: 2 ; α: 0
  -/
  | protected REVERT : SOp τ
  /--
    INVALID: invalid opcode
    δ: ∅ ; α: ∅
  -/
  | protected INVALID : SOp τ
  /--
    SELFDESTRUCT: halt and send entire balance to target.
    Deprecated; see EIP-6780
    δ: 1 ; α: 0
  -/
  | protected SELFDESTRUCT : SOp τ
  deriving DecidableEq, Repr

end Operation

end Operation

open Operation

inductive Operation : OperationType → Type where
  | protected StopArith    : SAOp   τ → Operation τ
  | protected CompBit      : CBLOp  τ → Operation τ
  | protected Keccak       : KOp    τ → Operation τ
  | protected Env          : EOp    τ → Operation τ
  | protected Block        : BOp    τ → Operation τ
  | protected StackMemFlow : SMSFOp τ → Operation τ
  | protected Push         : POp      → Operation .EVM
  | protected Dup          : DOp      → Operation .EVM
  | protected Exchange     : ExOp     → Operation .EVM
  | protected Log          : LOp    τ → Operation τ
  | protected System       : SOp    τ → Operation τ
  deriving DecidableEq, Repr
namespace Operation

@[match_pattern]
abbrev STOP       {τ : OperationType} : Operation τ := .StopArith .STOP
abbrev ADD        {τ : OperationType} : Operation τ := .StopArith .ADD
abbrev MUL        {τ : OperationType} : Operation τ := .StopArith .MUL
abbrev SUB        {τ : OperationType} : Operation τ := .StopArith .SUB
abbrev DIV        {τ : OperationType} : Operation τ := .StopArith .DIV
abbrev SDIV       {τ : OperationType} : Operation τ := .StopArith .SDIV
abbrev MOD        {τ : OperationType} : Operation τ := .StopArith .MOD
abbrev SMOD       {τ : OperationType} : Operation τ := .StopArith .SMOD
abbrev ADDMOD     {τ : OperationType} : Operation τ := .StopArith .ADDMOD
abbrev MULMOD     {τ : OperationType} : Operation τ := .StopArith .MULMOD
abbrev EXP        {τ : OperationType} : Operation τ := .StopArith .EXP
abbrev SIGNEXTEND {τ : OperationType} : Operation τ := .StopArith .SIGNEXTEND

abbrev LT     {τ : OperationType} : Operation τ := .CompBit .LT
abbrev GT     {τ : OperationType} : Operation τ := .CompBit .GT
abbrev SLT    {τ : OperationType} : Operation τ := .CompBit .SLT
abbrev SGT    {τ : OperationType} : Operation τ := .CompBit .SGT
abbrev EQ     {τ : OperationType} : Operation τ := .CompBit .EQ
abbrev ISZERO {τ : OperationType} : Operation τ := .CompBit .ISZERO
abbrev AND    {τ : OperationType} : Operation τ := .CompBit .AND
abbrev OR     {τ : OperationType} : Operation τ := .CompBit .OR
abbrev XOR    {τ : OperationType} : Operation τ := .CompBit .XOR
abbrev NOT    {τ : OperationType} : Operation τ := .CompBit .NOT
abbrev BYTE   {τ : OperationType} : Operation τ := .CompBit .BYTE
abbrev SHL    {τ : OperationType} : Operation τ := .CompBit .SHL
abbrev SHR    {τ : OperationType} : Operation τ := .CompBit .SHR
abbrev SAR    {τ : OperationType} : Operation τ := .CompBit .SAR

abbrev KECCAK256 {τ : OperationType} : Operation τ := .Keccak .KECCAK256

abbrev ADDRESS        {τ : OperationType} : Operation τ := .Env .ADDRESS
abbrev BALANCE        {τ : OperationType} : Operation τ := .Env .BALANCE
abbrev ORIGIN         {τ : OperationType} : Operation τ := .Env .ORIGIN
abbrev CALLER         {τ : OperationType} : Operation τ := .Env .CALLER
abbrev CALLVALUE      {τ : OperationType} : Operation τ := .Env .CALLVALUE
abbrev CALLDATALOAD   {τ : OperationType} : Operation τ := .Env .CALLDATALOAD
abbrev CALLDATASIZE   {τ : OperationType} : Operation τ := .Env .CALLDATASIZE
abbrev CALLDATACOPY   {τ : OperationType} : Operation τ := .Env .CALLDATACOPY
abbrev CODESIZE       {τ : OperationType} : Operation τ := .Env .CODESIZE
abbrev GASPRICE       {τ : OperationType} : Operation τ := .Env .GASPRICE
abbrev CODECOPY       {τ : OperationType} : Operation τ := .Env .CODECOPY
abbrev EXTCODECOPY    {τ : OperationType} : Operation τ := .Env .EXTCODECOPY
abbrev EXTCODESIZE    {τ : OperationType} : Operation τ := .Env .EXTCODESIZE
abbrev RETURNDATASIZE {τ : OperationType} : Operation τ := .Env .RETURNDATASIZE
abbrev RETURNDATACOPY {τ : OperationType} : Operation τ := .Env .RETURNDATACOPY
abbrev EXTCODEHASH    {τ : OperationType} : Operation τ := .Env .EXTCODEHASH

abbrev BLOCKHASH   {τ : OperationType} : Operation τ := .Block .BLOCKHASH
abbrev COINBASE    {τ : OperationType} : Operation τ := .Block .COINBASE
abbrev TIMESTAMP   {τ : OperationType} : Operation τ := .Block .TIMESTAMP
abbrev NUMBER      {τ : OperationType} : Operation τ := .Block .NUMBER
abbrev PREVRANDAO  {τ : OperationType} : Operation τ := .Block .PREVRANDAO
abbrev DIFFICULTY  {τ : OperationType} : Operation τ := .Block .DIFFICULTY
abbrev GASLIMIT    {τ : OperationType} : Operation τ := .Block .GASLIMIT
abbrev CHAINID     {τ : OperationType} : Operation τ := .Block .CHAINID
abbrev SELFBALANCE {τ : OperationType} : Operation τ := .Block .SELFBALANCE
abbrev BASEFEE     {τ : OperationType} : Operation τ := .Block .BASEFEE

abbrev POP     {τ : OperationType}   : Operation τ    := .StackMemFlow .POP
abbrev MLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .MLOAD
abbrev MSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE
abbrev SLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .SLOAD
abbrev SSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .SSTORE
abbrev MSTORE8 {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE8
abbrev JUMP                          : Operation .EVM := .StackMemFlow .JUMP
abbrev JUMPI                         : Operation .EVM := .StackMemFlow .JUMPI
abbrev PC                            : Operation .EVM    := .StackMemFlow .PC
abbrev MSIZE   {τ : OperationType}   : Operation τ    := .StackMemFlow .MSIZE
abbrev GAS     {τ : OperationType}   : Operation τ    := .StackMemFlow .GAS
abbrev JUMPDEST                      : Operation .EVM := .StackMemFlow .JUMPDEST
abbrev TLOAD   {τ : OperationType} : Operation τ    := .StackMemFlow .TLOAD
abbrev TSTORE  {τ : OperationType} : Operation τ    := .StackMemFlow .TSTORE
abbrev MCOPY   {τ : OperationType} : Operation τ := .StackMemFlow .MCOPY

abbrev PUSH0  : Operation .EVM := .Push .PUSH0
abbrev PUSH1  : Operation .EVM := .Push .PUSH1
abbrev PUSH2  : Operation .EVM := .Push .PUSH2
abbrev PUSH3  : Operation .EVM := .Push .PUSH3
abbrev PUSH4  : Operation .EVM := .Push .PUSH4
abbrev PUSH5  : Operation .EVM := .Push .PUSH5
abbrev PUSH6  : Operation .EVM := .Push .PUSH6
abbrev PUSH7  : Operation .EVM := .Push .PUSH7
abbrev PUSH8  : Operation .EVM := .Push .PUSH8
abbrev PUSH9  : Operation .EVM := .Push .PUSH9
abbrev PUSH10 : Operation .EVM := .Push .PUSH10
abbrev PUSH11 : Operation .EVM := .Push .PUSH11
abbrev PUSH12 : Operation .EVM := .Push .PUSH12
abbrev PUSH13 : Operation .EVM := .Push .PUSH13
abbrev PUSH14 : Operation .EVM := .Push .PUSH14
abbrev PUSH15 : Operation .EVM := .Push .PUSH15
abbrev PUSH16 : Operation .EVM := .Push .PUSH16
abbrev PUSH17 : Operation .EVM := .Push .PUSH17
abbrev PUSH18 : Operation .EVM := .Push .PUSH18
abbrev PUSH19 : Operation .EVM := .Push .PUSH19
abbrev PUSH20 : Operation .EVM := .Push .PUSH20
abbrev PUSH21 : Operation .EVM := .Push .PUSH21
abbrev PUSH22 : Operation .EVM := .Push .PUSH22
abbrev PUSH23 : Operation .EVM := .Push .PUSH23
abbrev PUSH24 : Operation .EVM := .Push .PUSH24
abbrev PUSH25 : Operation .EVM := .Push .PUSH25
abbrev PUSH26 : Operation .EVM := .Push .PUSH26
abbrev PUSH27 : Operation .EVM := .Push .PUSH27
abbrev PUSH28 : Operation .EVM := .Push .PUSH28
abbrev PUSH29 : Operation .EVM := .Push .PUSH29
abbrev PUSH30 : Operation .EVM := .Push .PUSH30
abbrev PUSH31 : Operation .EVM := .Push .PUSH31
abbrev PUSH32 : Operation .EVM := .Push .PUSH32

abbrev DUP1  : Operation .EVM := .Dup .DUP1
abbrev DUP2  : Operation .EVM := .Dup .DUP2
abbrev DUP3  : Operation .EVM := .Dup .DUP3
abbrev DUP4  : Operation .EVM := .Dup .DUP4
abbrev DUP5  : Operation .EVM := .Dup .DUP5
abbrev DUP6  : Operation .EVM := .Dup .DUP6
abbrev DUP7  : Operation .EVM := .Dup .DUP7
abbrev DUP8  : Operation .EVM := .Dup .DUP8
abbrev DUP9  : Operation .EVM := .Dup .DUP9
abbrev DUP10 : Operation .EVM := .Dup .DUP10
abbrev DUP11 : Operation .EVM := .Dup .DUP11
abbrev DUP12 : Operation .EVM := .Dup .DUP12
abbrev DUP13 : Operation .EVM := .Dup .DUP13
abbrev DUP14 : Operation .EVM := .Dup .DUP14
abbrev DUP15 : Operation .EVM := .Dup .DUP15
abbrev DUP16 : Operation .EVM := .Dup .DUP16

abbrev SWAP1  : Operation .EVM := .Exchange .SWAP1
abbrev SWAP2  : Operation .EVM := .Exchange .SWAP2
abbrev SWAP3  : Operation .EVM := .Exchange .SWAP3
abbrev SWAP4  : Operation .EVM := .Exchange .SWAP4
abbrev SWAP5  : Operation .EVM := .Exchange .SWAP5
abbrev SWAP6  : Operation .EVM := .Exchange .SWAP6
abbrev SWAP7  : Operation .EVM := .Exchange .SWAP7
abbrev SWAP8  : Operation .EVM := .Exchange .SWAP8
abbrev SWAP9  : Operation .EVM := .Exchange .SWAP9
abbrev SWAP10 : Operation .EVM := .Exchange .SWAP10
abbrev SWAP11 : Operation .EVM := .Exchange .SWAP11
abbrev SWAP12 : Operation .EVM := .Exchange .SWAP12
abbrev SWAP13 : Operation .EVM := .Exchange .SWAP13
abbrev SWAP14 : Operation .EVM := .Exchange .SWAP14
abbrev SWAP15 : Operation .EVM := .Exchange .SWAP15
abbrev SWAP16 : Operation .EVM := .Exchange .SWAP16

abbrev LOG0 {τ : OperationType} : Operation τ := .Log .LOG0
abbrev LOG1 {τ : OperationType} : Operation τ := .Log .LOG1
abbrev LOG2 {τ : OperationType} : Operation τ := .Log .LOG2
abbrev LOG3 {τ : OperationType} : Operation τ := .Log .LOG3
abbrev LOG4 {τ : OperationType} : Operation τ := .Log .LOG4

abbrev CREATE       {τ : OperationType} : Operation τ := .System .CREATE
abbrev CALL         {τ : OperationType} : Operation τ := .System .CALL
abbrev CALLCODE     {τ : OperationType} : Operation τ := .System .CALLCODE
abbrev RETURN       {τ : OperationType} : Operation τ := .System .RETURN
abbrev DELEGATECALL {τ : OperationType} : Operation τ := .System .DELEGATECALL
abbrev CREATE2      {τ : OperationType} : Operation τ := .System .CREATE2
abbrev STATICCALL   {τ : OperationType} : Operation τ := .System .STATICCALL
abbrev REVERT       {τ : OperationType} : Operation τ := .System .REVERT
abbrev INVALID      {τ : OperationType} : Operation τ := .System .INVALID
abbrev SELFDESTRUCT {τ : OperationType} : Operation τ := .System .SELFDESTRUCT

def isPush {τ : OperationType} : Operation τ → Bool
  | .Push _ => true
  | _ => false

def isJump {τ : OperationType} : Operation τ → Bool
  | .JUMP => true
  | .JUMPI => true
  | _ => false

def isPC {τ : OperationType} : Operation τ → Bool
  | .PC => true
  | _ => false

def isJumpdest {τ : OperationType} : Operation τ → Bool
  | .JUMPDEST => true
  | _ => false

def isDup {τ : OperationType} : Operation τ → Bool
  | .Dup _ => true
  | _ => false

def isSwap {τ : OperationType} : Operation τ → Bool
  | .Exchange _ => true
  | _ => false

def isCreate {τ : OperationType} : Operation τ → Bool
  | .CREATE => true
  | .CREATE2 => true
  | _ => false

def isCall {τ : OperationType} : Operation τ → Bool
  | .CALL => true
  | .CALLCODE => true
  | .DELEGATECALL => true
  | .STATICCALL => true
  | _ => false


end Operation

open EvmYul.UInt256

def exp (a b : UInt256) : UInt256 :=
  a ^ b.val

abbrev fromBool := Bool.toUInt256

def lt (a b : UInt256) :=
  fromBool (a < b)

def gt (a b : UInt256) :=
  fromBool (a > b)

-- def slt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.slt a b)

-- def sgt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.sgt a b)

def eq (a b : UInt256) :=
  fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (a = 0)

end EvmYul

open EvmYul

-- Apendix H, (320)
def M (s f l : UInt256) : UInt256 :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    let rem := (f + l) % 32
    let divided := (f + l) / 32
    max s (if rem == 0 then divided else divided + 1)
