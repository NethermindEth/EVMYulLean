import EvmYul.Operations

namespace EvmYul

namespace EVM

open Operation

def serializeStopArithInstr : SAOp .EVM → UInt8
  | .STOP       => 0x00
  | .ADD        => 0x01
  | .MUL        => 0x02
  | .SUB        => 0x03
  | .DIV        => 0x04
  | .SDIV       => 0x05
  | .MOD        => 0x06
  | .SMOD       => 0x07
  | .ADDMOD     => 0x08
  | .MULMOD     => 0x09
  | .EXP        => 0x0a
  | .SIGNEXTEND => 0x0b

def serializeCompBitInstr : CBLOp .EVM → UInt8
  | .LT     => 0x10
  | .GT     => 0x11
  | .SLT    => 0x12
  | .SGT    => 0x13
  | .EQ     => 0x14
  | .ISZERO => 0x15
  | .AND    => 0x16
  | .OR     => 0x17
  | .XOR    => 0x18
  | .NOT    => 0x19
  | .BYTE   => 0x1a
  | .SHL    => 0x1b
  | .SHR    => 0x1c
  | .SAR    => 0x1d

def serializeKeccakInstr : KOp .EVM → UInt8
  | .KECCAK256 => 0x20

def serializeEnvInstr : EOp .EVM → UInt8
  | .ADDRESS        => 0x30
  | .BALANCE        => 0x31
  | .ORIGIN         => 0x32
  | .CALLER         => 0x33
  | .CALLVALUE      => 0x34
  | .CALLDATALOAD   => 0x35
  | .CALLDATASIZE   => 0x36
  | .CALLDATACOPY   => 0x37
  | .CODESIZE       => 0x38
  | .CODECOPY       => 0x39
  | .GASPRICE       => 0x3a
  | .EXTCODESIZE    => 0x3b
  | .EXTCODECOPY    => 0x3c
  | .RETURNDATASIZE => 0x3d
  | .RETURNDATACOPY => 0x3e
  | .EXTCODEHASH    => 0x3f

def serializeBlockInstr : BOp .EVM → UInt8
  | .BLOCKHASH   => 0x40
  | .COINBASE    => 0x41
  | .TIMESTAMP   => 0x42
  | .NUMBER      => 0x43
  | .PREVRANDAO  => 0x44
  | .GASLIMIT    => 0x45
  | .CHAINID     => 0x46
  | .SELFBALANCE => 0x47
  | .BASEFEE     => 0x48
  | .BLOBHASH    => 0x49
  | .BLOBBASEFEE => 0x4a

def serializeStackMemFlowInstr : SMSFOp .EVM → UInt8
  | .POP      => 0x50
  | .MLOAD    => 0x51
  | .MSTORE   => 0x52
  | .MSTORE8  => 0x53
  | .SLOAD    => 0x54
  | .SSTORE   => 0x55
  | .JUMP     => 0x56
  | .JUMPI    => 0x57
  | .PC       => 0x58
  | .MSIZE    => 0x58
  | .GAS      => 0x5a
  | .JUMPDEST => 0x5b
  | .TLOAD    => 0x5c
  | .TSTORE   => 0x5d
  | .MCOPY    => 0x5e

def serializePushInstr : POp → UInt8
  | .PUSH0  => 0x5f
  | .PUSH1  => 0x60
  | .PUSH2  => 0x61
  | .PUSH3  => 0x62
  | .PUSH4  => 0x63
  | .PUSH5  => 0x64
  | .PUSH6  => 0x65
  | .PUSH7  => 0x66
  | .PUSH8  => 0x67
  | .PUSH9  => 0x68
  | .PUSH10 => 0x69
  | .PUSH11 => 0x6a
  | .PUSH12 => 0x6b
  | .PUSH13 => 0x6c
  | .PUSH14 => 0x6d
  | .PUSH15 => 0x6e
  | .PUSH16 => 0x6f
  | .PUSH17 => 0x70
  | .PUSH18 => 0x71
  | .PUSH19 => 0x72
  | .PUSH20 => 0x73
  | .PUSH21 => 0x74
  | .PUSH22 => 0x75
  | .PUSH23 => 0x76
  | .PUSH24 => 0x77
  | .PUSH25 => 0x78
  | .PUSH26 => 0x79
  | .PUSH27 => 0x7a
  | .PUSH28 => 0x7b
  | .PUSH29 => 0x7c
  | .PUSH30 => 0x7d
  | .PUSH31 => 0x7e
  | .PUSH32 => 0x7f

def serializeDupInstr : DOp → UInt8
  | .DUP1  => 0x80
  | .DUP2  => 0x81
  | .DUP3  => 0x82
  | .DUP4  => 0x83
  | .DUP5  => 0x84
  | .DUP6  => 0x85
  | .DUP7  => 0x86
  | .DUP8  => 0x87
  | .DUP9  => 0x88
  | .DUP10 => 0x89
  | .DUP11 => 0x8a
  | .DUP12 => 0x8b
  | .DUP13 => 0x8c
  | .DUP14 => 0x8d
  | .DUP15 => 0x8e
  | .DUP16 => 0x8f

def serializeSwapInstr : ExOp → UInt8
  | .SWAP1  => 0x90
  | .SWAP2  => 0x91
  | .SWAP3  => 0x92
  | .SWAP4  => 0x93
  | .SWAP5  => 0x94
  | .SWAP6  => 0x95
  | .SWAP7  => 0x96
  | .SWAP8  => 0x97
  | .SWAP9  => 0x98
  | .SWAP10 => 0x99
  | .SWAP11 => 0x9a
  | .SWAP12 => 0x9b
  | .SWAP13 => 0x9c
  | .SWAP14 => 0x9d
  | .SWAP15 => 0x9e
  | .SWAP16 => 0x9f

def serializeLogInstr : LOp .EVM → UInt8
  | .LOG0 => 0xa0
  | .LOG1 => 0xa1
  | .LOG2 => 0xa2
  | .LOG3 => 0xa3
  | .LOG4 => 0xa4

def serializeSysInstr : SOp .EVM → UInt8
  | .CREATE       => 0xf0
  | .CALL         => 0xf1
  | .CALLCODE     => 0xf2
  | .RETURN       => 0xf3
  | .DELEGATECALL => 0xf4
  | .CREATE2      => 0xf5
  | .STATICCALL   => 0xfa
  | .REVERT       => 0xfd
  | .INVALID      => 0xfe
  | .SELFDESTRUCT => 0xff

def serializeInstr : Operation .EVM → UInt8
  | .StopArith a    => serializeStopArithInstr a
  | .CompBit e      => serializeCompBitInstr e
  | .Keccak k       => serializeKeccakInstr k
  | .Env e          => serializeEnvInstr e
  | .Block b        => serializeBlockInstr b
  | .StackMemFlow m => serializeStackMemFlowInstr m
  | .Push p         => serializePushInstr p
  | .Dup d          => serializeDupInstr d
  | .Exchange e     => serializeSwapInstr e
  | .Log l          => serializeLogInstr l
  | .System s       => serializeSysInstr s

def δ : Operation .EVM → Option ℕ
  | .STOP           => some 0
  | .ADD            => some 2
  | .MUL            => some 2
  | .SUB            => some 2
  | .DIV            => some 2
  | .SDIV           => some 2
  | .MOD            => some 2
  | .SMOD           => some 2
  | .ADDMOD         => some 3
  | .MULMOD         => some 3
  | .EXP            => some 2
  | .SIGNEXTEND     => some 2
  | .LT             => some 2
  | .GT             => some 2
  | .SLT            => some 2
  | .SGT            => some 2
  | .EQ             => some 2
  | .ISZERO         => some 1
  | .AND            => some 2
  | .OR             => some 2
  | .XOR            => some 2
  | .NOT            => some 1
  | .BYTE           => some 2
  | .SHL            => some 2
  | .SHR            => some 2
  | .SAR            => some 2
  | .KECCAK256      => some 2
  | .ADDRESS        => some 0
  | .BALANCE        => some 1
  | .ORIGIN         => some 0
  | .CALLER         => some 0
  | .CALLVALUE      => some 0
  | .CALLDATALOAD   => some 1
  | .CALLDATASIZE   => some 0
  | .CALLDATACOPY   => some 3
  | .CODESIZE       => some 0
  | .CODECOPY       => some 3
  | .GASPRICE       => some 0
  | .EXTCODESIZE    => some 1
  | .EXTCODECOPY    => some 4
  | .RETURNDATASIZE => some 0
  | .RETURNDATACOPY => some 3
  | .EXTCODEHASH    => some 1
  | .BLOCKHASH      => some 1
  | .COINBASE       => some 0
  | .TIMESTAMP      => some 0
  | .NUMBER         => some 0
  | .PREVRANDAO     => some 0
  | .GASLIMIT       => some 0
  | .CHAINID        => some 0
  | .SELFBALANCE    => some 0
  | .BASEFEE        => some 0
  | .BLOBHASH       => some 1
  | .BLOBBASEFEE    => some 0
  | .POP            => some 1
  | .MLOAD          => some 1
  | .MSTORE         => some 2
  | .MSTORE8        => some 1
  | .SLOAD          => some 1
  | .SSTORE         => some 2
  | .PC             => some 0
  | .MSIZE          => some 0
  | .GAS            => some 0
  | .Push _         => some 0
  | .DUP1           => some 1
  | .DUP2           => some 2
  | .DUP3           => some 3
  | .DUP4           => some 4
  | .DUP5           => some 5
  | .DUP6           => some 6
  | .DUP7           => some 7
  | .DUP8           => some 8
  | .DUP9           => some 9
  | .DUP10          => some 10
  | .DUP11          => some 11
  | .DUP12          => some 12
  | .DUP13          => some 13
  | .DUP14          => some 14
  | .DUP15          => some 15
  | .DUP16          => some 16
  | .SWAP1          => some 2
  | .SWAP2          => some 3
  | .SWAP3          => some 4
  | .SWAP4          => some 5
  | .SWAP5          => some 6
  | .SWAP6          => some 7
  | .SWAP7          => some 8
  | .SWAP8          => some 9
  | .SWAP9          => some 10
  | .SWAP10         => some 11
  | .SWAP11         => some 12
  | .SWAP12         => some 13
  | .SWAP13         => some 14
  | .SWAP14         => some 15
  | .SWAP15         => some 16
  | .SWAP16         => some 17
  | .LOG0           => some 2
  | .LOG1           => some 3
  | .LOG2           => some 4
  | .LOG3           => some 5
  | .LOG4           => some 6
  | .JUMP           => some 1
  | .JUMPI          => some 2
  | .JUMPDEST       => some 0
  | .TLOAD          => some 1
  | .TSTORE         => some 2
  | .MCOPY          => some 3
  | .CREATE         => some 3
  | .CALL           => some 7
  | .CALLCODE       => some 7
  | .RETURN         => some 2
  | .DELEGATECALL   => some 6
  | .CREATE2        => some 4
  | .STATICCALL     => some 6
  | .REVERT         => some 2
  | .INVALID        => none
  | .SELFDESTRUCT   => some 1

def α : Operation .EVM → Option ℕ
  | .STOP => some 0
  | .ADD => some 1
  | .MUL => some 1
  | .SUB => some 1
  | .DIV => some 1
  | .SDIV => some 1
  | .MOD => some 1
  | .SMOD => some 1
  | .ADDMOD => some 1
  | .MULMOD => some 1
  | .EXP => some 1
  | .SIGNEXTEND  => some 1
  | .LT => some 1
  | .GT => some 1
  | .SLT  => some 1
  | .SGT => some 1
  | .EQ => some 1
  | .ISZERO => some 1
  | .AND => some 1
  | .OR => some 1
  | .XOR => some 1
  | .NOT => some 1
  | .BYTE => some 1
  | .SHL => some 1
  | .SHR => some 1
  | .SAR => some 1
  | .KECCAK256 => some 1
  | .ADDRESS => some 1
  | .BALANCE => some 1
  | .ORIGIN => some 1
  | .CALLER => some 1
  | .CALLVALUE => some 1
  | .CALLDATALOAD  => some 1
  | .CALLDATASIZE => some 1
  | .CALLDATACOPY => some 0
  | .CODESIZE  => some 1
  | .CODECOPY => some 0
  | .GASPRICE => some 1
  | .EXTCODESIZE  => some 1
  | .EXTCODECOPY => some 0
  | .RETURNDATASIZE  => some 1
  | .RETURNDATACOPY => some 0
  | .EXTCODEHASH => some 1
  | .BLOCKHASH => some 1
  | .COINBASE => some 1
  | .TIMESTAMP => some 1
  | .NUMBER => some 1
  | .PREVRANDAO => some 1
  | .GASLIMIT => some 1
  | .CHAINID => some 1
  | .SELFBALANCE => some 1
  | .BASEFEE => some 1
  | .BLOBHASH => some 1
  | .BLOBBASEFEE => some 1
  | .POP => some 0
  | .MLOAD => some 1
  | .MSTORE => some 0
  | .MSTORE8 => some 0
  | .SLOAD => some 1
  | .SSTORE => some 0
  | .PC => some 1
  | .MSIZE => some 1
  | .GAS => some 1
  | .JUMP => some 0
  | .JUMPI => some 0
  | .JUMPDEST => some 0
  | .TLOAD => some 1
  | .TSTORE => some 0
  | .MCOPY => some 0
  | .Push _ => some 1
  | .DUP1 => some 2
  | .DUP2 => some 3
  | .DUP3 => some 4
  | .DUP4 => some 5
  | .DUP5 => some 6
  | .DUP6 => some 7
  | .DUP7 => some 8
  | .DUP8 => some 9
  | .DUP9 => some 10
  | .DUP10 => some 11
  | .DUP11 => some 12
  | .DUP12 => some 13
  | .DUP13 => some 14
  | .DUP14 => some 15
  | .DUP15 => some 16
  | .DUP16 => some 16
  | .SWAP1 => some 2
  | .SWAP2 => some 3
  | .SWAP3 => some 4
  | .SWAP4 => some 5
  | .SWAP5 => some 6
  | .SWAP6 => some 7
  | .SWAP7 => some 8
  | .SWAP8 => some 9
  | .SWAP9 => some 10
  | .SWAP10 => some 11
  | .SWAP11 => some 12
  | .SWAP12 => some 13
  | .SWAP13 => some 14
  | .SWAP14 => some 15
  | .SWAP15 => some 16
  | .SWAP16 => some 17
  | .Log _ => some 0
  | .CREATE => some 1
  | .CALL => some 1
  | .CALLCODE => some 1
  | .RETURN => some 0
  | .DELEGATECALL => some 1
  | .CREATE2 => some 1
  | .STATICCALL => some 0
  | .REVERT => some 0
  | .INVALID => none
  | .SELFDESTRUCT => some 0

def parseInstr : UInt8 → Option (Operation .EVM)
  | 0x00 => some .STOP
  | 0x01 => some .ADD
  | 0x02 => some .MUL
  | 0x03 => some .SUB
  | 0x04 => some .DIV
  | 0x05 => some .SDIV
  | 0x06 => some .MOD
  | 0x07 => some .SMOD
  | 0x08 => some .ADDMOD
  | 0x09 => some .MULMOD
  | 0x0a => some .EXP
  | 0x0b => some .SIGNEXTEND

  | 0x10 => some .LT
  | 0x11 => some .GT
  | 0x12 => some .SLT
  | 0x13 => some .SGT
  | 0x14 => some .EQ
  | 0x15 => some .ISZERO
  | 0x16 => some .AND
  | 0x17 => some .OR
  | 0x18 => some .XOR
  | 0x19 => some .NOT
  | 0x1a => some .BYTE
  | 0x1b => some .SHL
  | 0x1c => some .SHR
  | 0x1d => some .SAR

  | 0x20 => some .KECCAK256

  | 0x30 => some .ADDRESS
  | 0x31 => some .BALANCE
  | 0x32 => some .ORIGIN
  | 0x33 => some .CALLER
  | 0x34 => some .CALLVALUE
  | 0x35 => some .CALLDATALOAD
  | 0x36 => some .CALLDATASIZE
  | 0x37 => some .CALLDATACOPY
  | 0x38 => some .CODESIZE
  | 0x39 => some .CODECOPY
  | 0x3a => some .GASPRICE
  | 0x3b => some .EXTCODESIZE
  | 0x3c => some .EXTCODECOPY
  | 0x3d => some .RETURNDATASIZE
  | 0x3e => some .RETURNDATACOPY
  | 0x3f => some .EXTCODEHASH

  | 0x40 => some .BLOCKHASH
  | 0x41 => some .COINBASE
  | 0x42 => some .TIMESTAMP
  | 0x43 => some .NUMBER
  | 0x44 => some .PREVRANDAO
  | 0x45 => some .GASLIMIT
  | 0x46 => some .CHAINID
  | 0x47 => some .SELFBALANCE
  | 0x48 => some .BASEFEE
  | 0x49 => some .BLOBHASH
  | 0x4a => some .BLOBBASEFEE

  | 0x50 => some .POP
  | 0x51 => some .MLOAD
  | 0x52 => some .MSTORE
  | 0x53 => some .MSTORE8
  | 0x54 => some .SLOAD
  | 0x55 => some .SSTORE
  | 0x56 => some .JUMP
  | 0x57 => some .JUMPI
  | 0x58 => some .PC
  | 0x59 => some .MSIZE
  | 0x5a => some .GAS
  | 0x5b => some .JUMPDEST
  | 0x5c => some .TLOAD
  | 0x5d => some .TSTORE
  | 0x5e => some .MCOPY

  | 0x5f => some .PUSH0
  | 0x60 => some .PUSH1
  | 0x61 => some .PUSH2
  | 0x62 => some .PUSH3
  | 0x63 => some .PUSH4
  | 0x64 => some .PUSH5
  | 0x65 => some .PUSH6
  | 0x66 => some .PUSH7
  | 0x67 => some .PUSH8
  | 0x68 => some .PUSH9
  | 0x69 => some .PUSH10
  | 0x6a => some .PUSH11
  | 0x6b => some .PUSH12
  | 0x6c => some .PUSH13
  | 0x6d => some .PUSH14
  | 0x6e => some .PUSH15
  | 0x6f => some .PUSH16
  | 0x70 => some .PUSH17
  | 0x71 => some .PUSH18
  | 0x72 => some .PUSH19
  | 0x73 => some .PUSH20
  | 0x74 => some .PUSH21
  | 0x75 => some .PUSH22
  | 0x76 => some .PUSH23
  | 0x77 => some .PUSH24
  | 0x78 => some .PUSH25
  | 0x79 => some .PUSH26
  | 0x7a => some .PUSH27
  | 0x7b => some .PUSH28
  | 0x7c => some .PUSH29
  | 0x7d => some .PUSH30
  | 0x7e => some .PUSH31
  | 0x7f => some .PUSH32

  | 0x80 => some .DUP1
  | 0x81 => some .DUP2
  | 0x82 => some .DUP3
  | 0x83 => some .DUP4
  | 0x84 => some .DUP5
  | 0x85 => some .DUP6
  | 0x86 => some .DUP7
  | 0x87 => some .DUP8
  | 0x88 => some .DUP9
  | 0x89 => some .DUP10
  | 0x8a => some .DUP11
  | 0x8b => some .DUP12
  | 0x8c => some .DUP13
  | 0x8d => some .DUP14
  | 0x8e => some .DUP15
  | 0x8f => some .DUP16

  | 0x90 => some .SWAP1
  | 0x91 => some .SWAP2
  | 0x92 => some .SWAP3
  | 0x93 => some .SWAP4
  | 0x94 => some .SWAP5
  | 0x95 => some .SWAP6
  | 0x96 => some .SWAP7
  | 0x97 => some .SWAP8
  | 0x98 => some .SWAP9
  | 0x99 => some .SWAP10
  | 0x9a => some .SWAP11
  | 0x9b => some .SWAP12
  | 0x9c => some .SWAP13
  | 0x9d => some .SWAP14
  | 0x9e => some .SWAP15
  | 0x9f => some .SWAP16

  | 0xa0 => some .LOG0
  | 0xa1 => some .LOG1
  | 0xa2 => some .LOG2
  | 0xa3 => some .LOG3
  | 0xa4 => some .LOG4

  | 0xf0 => some .CREATE
  | 0xf1 => some .CALL
  | 0xf2 => some .CALLCODE
  | 0xf3 => some .RETURN
  | 0xf4 => some .DELEGATECALL
  | 0xf5 => some .CREATE2
  | 0xfa => some .STATICCALL
  | 0xfd => some .REVERT
  | 0xfe => some .INVALID
  | 0xff => some .SELFDESTRUCT
  | _    => none

end EVM

end EvmYul
