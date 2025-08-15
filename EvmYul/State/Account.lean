import EvmYul.Maps.StorageMap
import EvmYul.SpongeHash.Keccak256

import EvmYul.UInt256
import EvmYul.Wheels

import EvmYul.Yul.Ast

namespace EvmYul

/--
  Precompiled contract addresses.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`
-/
def π : Batteries.RBSet AccountAddress compare :=
  Batteries.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare

inductive ToExecute (τ : OperationType) where
  | Code (code : match τ with
                   | .EVM => ByteArray
                   | .Yul => Yul.Ast.Stmt)
  | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState (τ : OperationType) where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : match τ with
              | .EVM => ByteArray
              | .Yul => Yul.Ast.Stmt

instance {τ} [Repr (match τ with | .EVM => ByteArray | .Yul => Yul.Ast.Stmt)] : Repr (PersistentAccountState τ) where
  reprPrec s _ :=
    let codeFmt :=
      match τ with
      | .EVM => reprPrec s.code 0
      | .Yul => reprPrec s.code 0
    s!"PersistentAccountState(nonce: {reprPrec s.nonce 0}, balance: {reprPrec s.balance 0}, storage: {reprPrec s.storage 0}, code: {codeFmt})"

instance {τ} : BEq (PersistentAccountState τ) where
  beq a b :=
       a.nonce == b.nonce
    && a.balance == b.balance
    && a.storage == b.storage
    && (match τ with
          | .EVM => a.code == b.code
          | .Yul => a.code == b.code)

instance {τ} : Inhabited (PersistentAccountState τ) where
  default := {
    nonce := default
    balance := default
    storage := default
    code := match τ with
            | .EVM => default
            | .Yul => default
  }

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account (τ : OperationType) extends PersistentAccountState τ where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState .EVM) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

def Account.codeHash (self : (Account .EVM)) : UInt256 :=
  self.toPersistentAccountState.codeHash

end EvmYul
