import EvmYul.State.SubstateOps
import EvmYul.State.AccountOps

import EvmYul.Maps.YPState

import EvmYul.State
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace State

def addAccessedAccount (self : State) (addr : AccountAddress) : State :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey (self : State) (sk : AccountAddress × UInt256) : State :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.

def accountExists (self : State) (addr : AccountAddress) : Bool := self.accountMap.lookup addr |>.isSome
TODO - some conundrum about the mismatch of particulars of states from YP, maybe this should not be here
-/
def dead (σ : YPState) (addr : AccountAddress) : Bool :=
  σ.find? addr |>.option True Account.emptyAccount

def accountExists (self : State) (addr : AccountAddress) : Bool := self.accountMap.find? addr |>.isSome

def lookupAccount (self : State) (addr : AccountAddress) : Option Account :=
  self.accountMap.find? addr

def updateAccount (addr : AccountAddress) (act : Account) (self : State) : State :=
  { self with accountMap := self.accountMap.insert addr act }

def setAccount (self : State) (addr : AccountAddress) (acc : Account) : State :=
  { self with accountMap := self.accountMap.insert addr acc }

def setSelfAccount (self : State) (acc : Account := default) : State :=
  self.setAccount self.executionEnv.codeOwner acc

def updateAccount! (self : State) (addr : AccountAddress) (f : Account → Account) : State :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def updateSelfAccount! (self : State) : (Account → Account) → State :=
  self.updateAccount! self.executionEnv.codeOwner

def balance (self : State) (k : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accountMap.find? addr |>.elim ⟨0⟩ Account.balance)

-- def transferBalance (sender : AccountAddress) (recipient : AccountAddress) (balance : UInt256) (self : State) : Option State :=
--   if sender == recipient then .some self -- NB this check renders `balance` validity irrelevant
--   else do
--     let senderAcc ← self.accountMap.find? sender
--     let recipientAcc ← self.accountMap.find? recipient
--     let (senderAcc, recipientAcc) ← senderAcc.transferBalanceTo balance recipientAcc
--     self.updateAccount sender senderAcc
--       |>.updateAccount recipient recipientAcc

def initialiseAccount (addr : AccountAddress) (self : State) : State :=
  if self.accountExists addr then self else self.updateAccount addr default

-- def setBalance! (self : State) (addr : AccountAddress) (balance : UInt256) : State :=
--   self.updateAccount! addr (λ acc ↦ { acc with balance := balance })

-- def setSelfBalance! (self : State) : UInt256 → State :=
--   self.setBalance! self.executionEnv.codeOwner

def calldataload (self : State) (v : UInt256) : UInt256 :=
  -- dbg_trace s!"calldataload arr: {self.executionEnv.inputData.extract' v (v + 32)}"
  -- dbg_trace s!"calldataload yielding: {toHex <| self.executionEnv.inputData.extract' v (v + 32)}"
  uInt256OfByteArray <| self.executionEnv.inputData.readBytes v.toNat 32

def setNonce! (self : State) (addr : AccountAddress) (nonce : UInt256) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

def setSelfNonce! (self : State) (nonce : UInt256) : State :=
  self.setNonce! self.executionEnv.codeOwner nonce

def selfStorage! (self : State) : Storage :=
  self.lookupAccount self.executionEnv.codeOwner |>.getD default |>.storage

section CodeCopy

def extCodeSize (self : State) (a : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ Account.code)
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State) (v : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accountMap addr then (newState, ⟨0⟩) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option ⟨0⟩ Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash (self : State) (blockNumber : UInt256) : UInt256 :=
  -- TODO: Not 100% sure
  let v := self.executionEnv.header.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then ⟨0⟩
  else
    let hashes :=
      #[self.genesisBlockHeader.hash] ++ self.blocks.map (BlockHeader.hash ∘ Block.blockHeader)
    hashes.getD 0 blockNumber

def coinBase (self : State) : AccountAddress :=
  self.executionEnv.header.beneficiary

def timeStamp (self : State) : UInt256 :=
  -- dbg_trace self.executionEnv.header.timestamp
  .ofNat self.executionEnv.header.timestamp

def number (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.number

def difficulty (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.difficulty

def gasLimit (self : State) : UInt256 :=
  .ofNat self.executionEnv.header.gasLimit

def chainId (self : State) : UInt256 :=
  self.executionEnv.header.chainId

def selfbalance (self : State) : UInt256 :=
  Batteries.RBMap.find? self.accountMap self.executionEnv.codeOwner |>.elim ⟨0⟩ Account.balance

/--
TODO: `Account` also has `code`. Recheck.
-/
def setCode (self : State) (code : ByteArray) : State :=
  { self with executionEnv.code := code }

end Blocks

section Storage

def setStorage! (self : State) (addr : AccountAddress) (strg : Storage) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def setSelfStorage! (self : State) : Storage → State :=
  self.setStorage! self.executionEnv.codeOwner

def sload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

def sstore (self : State) (spos sval : UInt256) : State :=
  let Iₐ := self.executionEnv.codeOwner
  let { storage := σ, ostorage := σ₀, .. } := self.accountMap.find! Iₐ
  let v₀ := σ₀.findD spos ⟨0⟩
  let v := σ.findD spos ⟨0⟩
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

def tload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupTransientStorage (k := spos))
  (self, v)

def tstore (self : State) (spos sval : UInt256) : State :=
  -- TODO: "If the `TSTORE` opcode is called within the context of a `STATICCALL`,
  -- it will result in an exception instead of performing the modification."
  -- Not any static call (i.e. perm = 0)?
  let Iₐ := self.executionEnv.codeOwner
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)


end Storage

end State

end EvmYul
