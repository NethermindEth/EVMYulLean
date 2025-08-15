import EvmYul.State.SubstateOps
import EvmYul.State.AccountOps

import EvmYul.Maps.AccountMap

import EvmYul.State
import EvmYul.Wheels
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace State

def addAccessedAccount {τ} (self : State τ) (addr : AccountAddress) : State τ :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey {τ} (self : State τ) (sk : AccountAddress × UInt256) : State τ :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.
-/
def dead {τ} (σ : AccountMap τ) (addr : AccountAddress) : Bool :=
  σ.find? addr |>.option True Account.emptyAccount

def accountExists {τ} (self : State τ) (addr : AccountAddress) : Bool := self.accountMap.find? addr |>.isSome

def lookupAccount {τ} (self : State τ) (addr : AccountAddress) : Option (Account τ) :=
  self.accountMap.find? addr

def updateAccount {τ} (addr : AccountAddress) (act : Account τ) (self : State τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr act }

def setAccount {τ} (self : State τ) (addr : AccountAddress) (acc : Account τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr acc }

def setSelfAccount {τ} (self : State τ) (acc : Account τ := default) : State τ :=
  self.setAccount self.executionEnv.codeOwner acc

def updateAccount! {τ} (self : State τ) (addr : AccountAddress) (f : Account τ → Account τ) : State τ :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def updateSelfAccount! {τ} (self : State τ) : (Account τ → Account τ) → State τ :=
  self.updateAccount! self.executionEnv.codeOwner

def balance {τ} (self : State τ) (k : UInt256) : State τ × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accountMap.find? addr |>.elim ⟨0⟩ (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State .EVM) : State .EVM :=
  if self.accountExists addr then self else self.updateAccount addr default

def calldataload {τ} (self : State τ) (v : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.inputData.readBytes v.toNat 32

def setNonce! {τ} (self : State τ) (addr : AccountAddress) (nonce : UInt256) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

def setSelfNonce! {τ} (self : State τ) (nonce : UInt256) : State τ :=
  self.setNonce! self.executionEnv.codeOwner nonce

def selfStorage! {τ} (self : State τ) : Storage :=
  self.lookupAccount self.executionEnv.codeOwner |>.getD default |>.storage

section CodeCopy

def extCodeSize (self : State .EVM) (a : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State .EVM) (v : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accountMap addr then (newState, ⟨0⟩) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option ⟨0⟩ Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash {τ} (self : State τ) (blockNumber : UInt256) : UInt256 :=
  let v := self.executionEnv.header.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then ⟨0⟩
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat ⟨0⟩

def coinBase {τ} (self : State τ) : AccountAddress :=
  self.executionEnv.header.beneficiary

def timeStamp {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.timestamp

def number {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.number

def difficulty {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.difficulty

def gasLimit {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.gasLimit

def chainId {τ} (_ : State τ) : UInt256 := .ofNat EvmYul.chainId

def selfbalance {τ} (self : State τ) : UInt256 :=
  Batteries.RBMap.find? self.accountMap self.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)

def setCode (self : State .EVM) (code : ByteArray) : State .EVM :=
  { self with executionEnv.code := code }

end Blocks

section Storage

def setStorage! {τ} (self : State τ) (addr : AccountAddress) (strg : Storage) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def setSelfStorage! {τ} (self : State τ) : Storage → State τ :=
  self.setStorage! self.executionEnv.codeOwner

def sload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

def sstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  let { storage := σ_Iₐ, .. } := self.accountMap.find! Iₐ
  let v₀ :=
    match self.σ₀.find? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.findD spos ⟨0⟩
  let v := σ_Iₐ.findD spos ⟨0⟩
  let v' := sval

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let newAᵣ : UInt256 :=
    match ΔAᵣ with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - ⟨1⟩
  self.lookupAccount Iₐ |>.option self λ acc ↦
    let self' :=
      self.setAccount Iₐ (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (Iₐ, spos)
    { self' with substate.refundBalance := newAᵣ }

def tload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupTransientStorage (k := spos))
  (self, v)

def tstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)

end Storage

end State

end EvmYul
