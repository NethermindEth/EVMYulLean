import Mathlib.Data.List.Intervals

import EvmYul.UInt256
import EvmYul.EVM.State
import EvmYul.State.AccountOps
import EvmYul.StateOps

namespace EvmYul

namespace EVM

namespace State

section Instructions

def incrPC (I : EVM.State) (pcΔ : ℕ := 1) : EVM.State :=
  { I with pc := I.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (I : EVM.State) (s : Stack UInt256) (pcΔ : ℕ := 1) : EVM.State :=
  incrPC { I with stack := s } pcΔ

end Instructions

def liftMState {m} [Monad m] (f : EvmYul.State .EVM → m (EvmYul.State .EVM)) : EVM.State → m EVM.State :=
  λ s ↦ do pure { s with toState := ← f s.toState }

instance {m} [Monad m] : CoeFun (EvmYul.State .EVM → m (EvmYul.State .EVM)) (λ _ ↦ EVM.State → m EVM.State) := ⟨liftMState⟩

def liftState (f : EvmYul.State .EVM → EvmYul.State .EVM) : EVM.State → EVM.State :=
  liftMState (m := Id) f

instance : CoeFun (EvmYul.State .EVM → EvmYul.State .EVM) (λ _ ↦ EVM.State → EVM.State) := ⟨liftState⟩

def initialiseAccount (addr : AccountAddress) : EVM.State → EVM.State :=
  EvmYul.State.initialiseAccount addr

def updateAccount (addr : AccountAddress) (act : Account .EVM) : EVM.State → EVM.State :=
  EvmYul.State.updateAccount addr act

def isEmpty (self : EVM.State) : Bool := self.toState.accountMap == ∅

end State

end EVM

end EvmYul
