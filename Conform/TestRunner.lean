import EvmYul.EVM.State
import EvmYul.EVM.Semantics
import EvmYul.EVM.Gas
import EvmYul.Wheels

import EvmYul.State.TransactionOps
import EvmYul.State.Withdrawal

import EvmYul.Maps.AccountMap

import EvmYul.Pretty
import EvmYul.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace EvmYul

namespace Conform

def VerySlowTests : Array String :=
  #[
    -- TODO: Is https://eips.ethereum.org/EIPS/eip-7623 relevant?
    "sha3_d3g0v0_Cancun" -- ~6MB getting keccak256'd, estimated time on my PC: ~1 hour, best guess: unfoldr.go in keccak256.lean
  , "CALLBlake2f_MaxRounds_d0g0v0_Cancun"
  ]

def GlobalBlacklist : Array String := VerySlowTests

def Pre.toEVMState (self : Pre) : EVM.State :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account :=
      {
        tstorage := ∅ -- TODO - Look into transaciton storage.
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage.toEvmYulStorage
        ostorage := acc.storage.toEvmYulStorage -- Remember the original storage.
      }
    { s with toState := s.setAccount addr account }

def Test.toTests (self : Test) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → EVM.State := Pre.toEVMState

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

private def compareWithEVMdefaults (s₁ s₂ : EvmYul.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if s.contains ⟨0⟩ then s else s.insert ⟨0⟩ ⟨0⟩

/--
TODO - This should be a generic map complement, but we are not trying to write a library here.

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageComplement (m₁ m₂ : AccountMap) : AccountMap := Id.run do
  let mut result : AccountMap := m₁
  for ⟨k₂, v₂⟩ in m₂.toList do
    match m₁.find? k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`.
Effectively `m₁ / m₂ × m₂ / m₁`.

- if the `Δ = (∅, ∅)`, then `m₁ = m₂`
- used for reporting delta between expected post state and the actual state post execution

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageΔ (m₁ m₂ : AccountMap) : AccountMap × AccountMap :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

section

/--
This section exists for debugging / testing mostly. It's somewhat ad-hoc.
-/

notation "TODO" => default

private def almostBEqButNotQuiteEvmYulState (s₁ s₂ : AddrMap AccountEntry) : Except String Bool := do
  -- let s₁ := bashState s₁
  -- let s₂ := bashState s₂
  if s₁ == s₂ then .ok true else throw "state mismatch"
--  where
--   bashState (s : AddrMap AccountEntry) : AddrMap AccountEntry :=
--     s.map
--       λ (addr, acc) ↦ (addr, { acc with balance := TODO })
/--
NB it is ever so slightly more convenient to be in `Except String Bool` here rather than `Option String`.

This is morally `s₁ == s₂` except we get a convenient way to both tune what is being compared
as well as report fine grained errors.
-/
private def almostBEqButNotQuite (s₁ s₂ : AddrMap AccountEntry) : Except String Bool := do
  discard <| almostBEqButNotQuiteEvmYulState s₁ s₂
  pure true -- Yes, we never return false, because we throw along the way. Yes, this is `Option`.

end

def executeTransaction (transaction : Transaction) (s : EVM.State) (header : BlockHeader) : Except EVM.Exception EVM.State := do
  let _TODOfuel := 2^13

  let (ypState, substate, z) ← EVM.Υ (debugMode := false) _TODOfuel s.accountMap header.chainId.toNat header.baseFeePerGas header s.genesisBlockHeader s.blocks transaction transaction.base.expectedSender

  -- as EIP 4788 (https://eips.ethereum.org/EIPS/eip-4788).

  -- TODO - I think we do this tuple → EVM.State conversion reasonably often, factor out?
  let result : EVM.State := {
    s with accountMap := ypState
           substate := substate
           executionEnv.perm := z -- TODO - that's probably not this :)
           -- returnData := TODO?
  }
  pure result


def validateTransaction
  (σ : AccountMap)
  (chainId : ℕ)
  (header : BlockHeader)
  (expectedSender : AccountAddress)
  (T : Transaction)
  : Except EVM.Exception Unit
:= do
  if T.base.nonce.toNat ≥ 2^64-1 then
    .error <| .TransactionException .NONCE_IS_MAX

  let g₀ : ℕ := EVM.intrinsicGas T
  if T.base.gasLimit.toNat < g₀ then
    .error <| .TransactionException .INTRINSIC_GAS_TOO_LOW

  match T with
    | .blob t =>
      if t.maxFeePerBlobGas.toNat < header.getBlobGasprice then .error (.TransactionException .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS)
      match t.blobVersionedHashes with
        | [] => .error (.TransactionException .TYPE_3_TX_ZERO_BLOBS)
        | hs =>
          if hs.any (λ h ↦ h[0]? != .some VERSIONED_HASH_VERSION_KZG) then
            .error (.TransactionException .TYPE_3_TX_ZERO_BLOBS)
    | .dynamic t =>
      if t.maxPriorityFeePerGas > t.maxFeePerGas then .error <| .TransactionException .InconsistentFees
    | _ => pure ()

  match T.base.recipient with
    | none => do
      let MAX_CODE_SIZE := 24576
      let MAX_INITCODE_SIZE := 2 * MAX_CODE_SIZE
      if T.base.data.size > MAX_INITCODE_SIZE then
        .error <| .TransactionException .INITCODE_SIZE_EXCEEDED
    | some _ => pure ()

  let H_f := header.baseFeePerGas
  let some T_RLP := RLP (← (L_X T)) | .error <| .TransactionException .IllFormedRLP

  -- let g₀ : ℕ := EVM.intrinsicGas T

  -- if T.base.gasLimit.toNat < g₀ then
  --   .error <| .TransactionException .INTRINSIC_GAS_TOO_LOW

  let r : ℕ := fromBytesBigEndian T.base.r.data.data
  let s : ℕ := fromBytesBigEndian T.base.s.data.data
  if 0 ≥ r ∨ r ≥ secp256k1n then .error <| .TransactionException .InvalidSignature
  if 0 ≥ s ∨ s > secp256k1n / 2 then .error <| .TransactionException .InvalidSignature
  let v : ℕ := -- (324)
    match T with
      | .legacy t =>
        let w := t.w.toNat
        if w ∈ [27, 28] then
          w - 27
        else
          if w = 35 + chainId * 2 ∨ w = 36 + chainId * 2 then
            (w - 35) % 2 -- `chainId` not subtracted in the Yellow paper but in the EEL spec
          else
            w
      | .access t | .dynamic t | .blob t => t.yParity.toNat
  if v ∉ [0, 1] then .error <| .TransactionException .InvalidSignature

  let h_T := -- (318)
    match T with
      | .legacy _ => KEC T_RLP
      | _ => KEC <| ByteArray.mk #[T.type] ++ T_RLP

  let (S_T : AccountAddress) ← -- (323)
    match ECDSARECOVER h_T (ByteArray.mk #[.ofNat v]) T.base.r T.base.s with
      | .ok s =>
        pure <| Fin.ofNat <| fromBytesBigEndian <|
          ((KEC s).extract 12 32 /- 160 bits = 20 bytes -/ ).data.data
      | .error s => .error <| .SenderRecoverError s
  if S_T != expectedSender then
    dbg_trace s!"Recovered sender ({EvmYul.toHex S_T.toByteArray}) ≠ expected sender ({EvmYul.toHex expectedSender.toByteArray})"
  -- dbg_trace s!"Looking for S_T: {S_T} in: σ: {repr σ}"

  -- "Also, with a slight abuse of notation ... "
  let (senderCode, senderNonce, senderBalance) :=
    match σ.find? S_T with
      | some sender => (sender.code, sender.nonce, sender.balance)
      | none =>
        dbg_trace s!"could not find sender {EvmYul.toHex S_T.toByteArray}"
        (.empty, ⟨0⟩, ⟨0⟩)


  if senderCode ≠ .empty then .error <| .TransactionException .SENDER_NOT_EOA
  if T.base.nonce < senderNonce  then .error <| .TransactionException .NONCE_MISMATCH_TOO_LOW
  if T.base.nonce > senderNonce then .error <| .TransactionException .NONCE_MISMATCH_TOO_HIGH
  let v₀ :=
    match T with
      | .legacy t | .access t => t.gasLimit * t.gasPrice + t.value
      | .dynamic t => t.gasLimit * t.maxFeePerGas + t.value
      | .blob t    => t.gasLimit * t.maxFeePerGas + t.value + (UInt256.ofNat <| (getTotalBlobGas T).getD 0) * t.maxFeePerBlobGas
  -- dbg_trace s!"v₀: {v₀}, senderBalance: {senderBalance}"
  if v₀ > senderBalance then .error <| .TransactionException .INSUFFICIENT_ACCOUNT_FUNDS

  if H_f >
    match T with
      | .dynamic t | .blob t => t.maxFeePerGas.toNat
      | .legacy t | .access t => t.gasPrice.toNat
  then .error <| .TransactionException .BaseFeeTooHigh

  let n :=
    match T.base.recipient with
      | some _ => T.base.data.size
      | none => 0
  if n > 49152 then .error <| .TransactionException .INITCODE_SIZE_EXCEEDED

 where
  L_X (T : Transaction) : Except EVM.Exception 𝕋 := -- (317)
    let accessEntryRLP : AccountAddress × Array UInt256 → 𝕋
      | ⟨a, s⟩ => .𝕃 [.𝔹 (AccountAddress.toByteArray a), .𝕃 (s.map (𝕋.𝔹 ∘ UInt256.toByteArray)).toList]
    let accessEntriesRLP (aEs : List (AccountAddress × Array UInt256)) : 𝕋 :=
      .𝕃 (aEs.map accessEntryRLP)
    match T with
      | /- 0 -/ .legacy t =>
        if t.w.toNat ∈ [27, 28] then
          .ok ∘ .𝕃 ∘ List.map .𝔹 <|
            [ BE t.nonce.toNat -- Tₙ
            , BE t.gasPrice.toNat -- Tₚ
            , BE t.gasLimit.toNat -- T_g
            , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
              t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
            , BE t.value.toNat -- Tᵥ
            , t.data
            ]
        else
          if t.w = .ofNat (35 + chainId * 2) ∨ t.w = .ofNat (36 + chainId * 2) then
            .ok ∘ .𝕃 ∘ List.map .𝔹 <|
              [ BE t.nonce.toNat -- Tₙ
              , BE t.gasPrice.toNat -- Tₚ
              , BE t.gasLimit.toNat -- T_g
              , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
                t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
              , BE t.value.toNat -- Tᵥ
              , t.data -- p
              , BE chainId
              , .empty
              , .empty
              ]
          else
            dbg_trace "IllFormedRLP legacy transacion: Tw = {t.w}; chainId = {chainId}"
            .error <| .TransactionException .IllFormedRLP

      | /- 1 -/ .access t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.gasPrice.toNat) -- Tₚ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- T_v
          , .𝔹 t.data  -- p
          , accessEntriesRLP <| Batteries.RBSet.toList t.accessList -- T_A
          ]
      | /- 2 -/ .dynamic t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP <| Batteries.RBSet.toList t.accessList -- T_A
          ]
      | /- 3 -/ .blob t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP <| Batteries.RBSet.toList t.accessList -- T_A
          , .𝔹 (BE t.maxFeePerBlobGas.toNat)
          , .𝕃 (t.blobVersionedHashes.map .𝔹)
          ]

def validateBlock (parentHeader : BlockHeader) (block : Block)
  : Except EVM.Exception (Transactions × Withdrawals)
:= do
  -- dbg_trace "VALIDATING BLOCK"
  if calcExcessBlobGas parentHeader != block.blockHeader.excessBlobGas then
    throw <| .BlockException .INCORRECT_EXCESS_BLOB_GAS

  match block.blockHeader.blobGasUsed, block.blockHeader.excessBlobGas with
  | some _, none | none, some _ =>
    throw <| .BlockException .INCORRECT_BLOCK_FORMAT
  | _, _ => pure ()

  let blobGasUsed := List.sum <| Array.data <| block.transactions.map ((Option.getD · 0) ∘  getTotalBlobGas)

  match block.blockHeader.blobGasUsed with
    | none => pure ()
    | some bGU =>
      if blobGasUsed != bGU.toNat then
        throw <| .BlockException .INCORRECT_BLOB_GAS_USED

  let MAX_BLOB_GAS_PER_BLOCK := 786432
  if blobGasUsed > MAX_BLOB_GAS_PER_BLOCK then
    throw <| .BlockException .BLOB_GAS_USED_ABOVE_LIMIT

  if block.blockHeader.withdrawalsRoot.isSome && computeTrieRoot block.withdrawals ≠ block.blockHeader.withdrawalsRoot then
    throw <| .BlockException .INVALID_WITHDRAWALS_ROOT

  -- dbg_trace "BLOCK VALID"
  pure (block.transactions, block.withdrawals)
/--
This assumes that the `transactions` are ordered, as they should be in the test suit.
-/
def processBlocks (s₀ : EVM.State) : Except EVM.Exception EVM.State := do
  let blocks := s₀.blocks
  let parentHeaders := #[s₀.genesisBlockHeader] ++ blocks.map Block.blockHeader
  let withParentHeaders := parentHeaders.zip blocks

  withParentHeaders.foldlM processBlock s₀
 where
  processBlock (s₀ : EVM.State) (withParentHeader : BlockHeader × Block) : Except EVM.Exception EVM.State := do
    let (parentHeader, block) := withParentHeader
    let (encounteredBlockException, transactions, s, withdrawals) ←
      match validateBlock parentHeader block with
        | .error e =>
          if block.exception.containsSubstr (repr e).pretty then
            dbg_trace s!"Expected exception: {block.exception}; got exception: {repr e}"
            pure (true, #[], s₀, #[])
          else
            throw e
        | .ok (ts, ws) =>
          let BEACON_ROOTS_ADDRESS : AccountAddress := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
          let SYSTEM_ADDRESS : AccountAddress := 0xfffffffffffffffffffffffffffffffffffffffe
          let s ←
          match s₀.accountMap.find? BEACON_ROOTS_ADDRESS with
            | none => pure (false, ts, s₀, ws)
            | some roots =>
              let beaconRootsAddressCode := roots.code
              let _TODOfuel := 2^13
              -- the call does not count against the block’s gas limit
              let beaconCallResult :=
                EVM.Θ (debugMode := false) _TODOfuel
                  []
                  .empty
                  s₀.genesisBlockHeader
                  s₀.blocks
                  s₀.accountMap
                  default
                  SYSTEM_ADDRESS
                  SYSTEM_ADDRESS
                  BEACON_ROOTS_ADDRESS
                  (.Code beaconRootsAddressCode)
                  ⟨30000000⟩
                  ⟨0xe8d4a51000⟩
                  ⟨0⟩
                  ⟨0⟩
                  block.blockHeader.parentBeaconBlockRoot
                  0
                  block.blockHeader
                  true
              let (createdAccounts, σ, substate) ←
                match beaconCallResult with
                  | .ok (createdAccounts, σ, _, substate, _ /- can't fail-/, _) =>
                    pure (createdAccounts, σ, substate)
                  | .error e => .error <| .ExecutionException e
              let s :=
                {s₀ with
                  createdAccounts := createdAccounts
                  accountMap := σ
                  substate := substate
                }
              pure (false, ts, s, ws)

    -- dbg_trace "\nStarting transactions"
    let (encounteredTransactionException, s) ←
      try
        let s ←
          transactions.foldlM
            (λ s' trans ↦ do
              validateTransaction s'.accountMap block.blockHeader.chainId.toNat block.blockHeader trans.base.expectedSender trans
              executeTransaction trans s' block.blockHeader
            )
            s
        let σ := applyWithdrawals s.accountMap withdrawals
        pure <| (false, { s with accountMap := σ })
      catch e =>
        if block.exception.containsSubstr (repr e).pretty then
          dbg_trace s!"Expected exception: {block.exception}; got exception: {repr e}"
          pure (true, s₀)
        else throw e

    if ¬encounteredBlockException && ¬encounteredTransactionException && ¬block.exception.isEmpty then
      throw <| .MissedExpectedException block.exception
    pure s


/--
- `.none` on success
- `.some endState` on failure

NB we can throw away the final state if it coincided with the expected one, hence `.none`.
-/
def preImpliesPost (pre : Pre) (post : Post) (genesisBlockHeader : BlockHeader) (blocks : Blocks) : Except EVM.Exception (Option AccountMap) := do
    let resultState ← processBlocks {pre.toEVMState with blocks := blocks, genesisBlockHeader := genesisBlockHeader}
    let result : AddrMap AccountEntry :=
      resultState.toState.accountMap.foldl
        (λ r addr ⟨nonce, balance, storage, _, _, code⟩ ↦ r.insert addr ⟨nonce, balance, storage, code⟩) default
    match almostBEqButNotQuite post result with
      | .error e =>
        dbg_trace e
        pure (.some resultState.accountMap) -- Feel free to inspect this error from `almostBEqButNotQuite`.
      | .ok _ => pure .none

-- local instance : MonadLift (Except EVM.Exception) (Except Conform.Exception) := ⟨Except.mapError .EVMError⟩
-- vvvvvvvvvvvvvv DO NOT DELETE PLEASE vvvvvvvvvvvvvvvvvv
def DONOTDELETEMEFORNOW : AccountMap := Batteries.RBMap.ofList [(1, { dflt with storage := Batteries.RBMap.ofList [(⟨44⟩, ⟨45⟩), (⟨46⟩, ⟨47⟩)] compare }), (3, default)] compare
  where dflt : Account := default

instance (priority := high) : Repr AccountMap := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(EvmYul.toHex k.toByteArray) /-|>.takeRight 5-/}]\n"
      result := result ++ s!"balance: {v.balance}\nnonce: {v.nonce}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩

def processTest (entry : TestEntry) (verbose : Bool := true) : TestResult := do
  let result := preImpliesPost entry.pre entry.postState entry.genesisBlockHeader entry.blocks
  match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => errorF <$> result

  where discardError : AccountMap → String := λ _ ↦ "ERROR."
        verboseError : AccountMap → String := λ σ ↦
          let (postSubActual, actualSubPost) := storageΔ entry.postState.toEVMState.accountMap σ
          s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
        errorF := if verbose then verboseError else discardError

local instance : MonadLift (Except String) (Except Conform.Exception) := ⟨Except.mapError .CannotParse⟩

def processTestsOfFile (file : System.FilePath)
                       (whitelist : Array String := #[])
                       (blacklist : Array String := #[]) :
                       ExceptT Exception IO (Batteries.RBMap String TestResult compare) := do
  let path := file
  let file ← Lean.Json.fromFile file
  let test ← Lean.FromJson.fromJson? (α := Test) file
  let tests := test.toTests
  let cancunTests := guardCancum tests
  -- dbg_trace s!"Non Cancun tests ignored: {tests.length - cancunTests.length}"
  let tests := guardBlacklist ∘ guardWhitelist <| cancunTests
  -- dbg_trace s!"tests after guard: {tests.map Prod.fst}"
  tests.foldlM (init := ∅) λ acc (testname, test) ↦
    dbg_trace s!"TESTING {testname} FROM {path}"
    -- dbg_trace s!"network : {test.network}"
    pure <| acc.insert testname (processTest test)
    -- try
    --   processTest test >>= pure ∘
    --   -- TODO currently the soft errors are the ones I am personally unsure about :)
    -- catch
    --   | e => pure (acc.insert testname (.mkFailed s!"{repr e}"))
    -- -- catch | .EVMError e@(.ReceiverNotInAccounts _) => pure (acc.insert testname (.mkFailed s!"{repr e}"))
    -- --       | e => throw e -- hard error, stop executing the tests; malformed input, logic error, etc.
    -- --                      -- This should not happen but makes cause analysis easier if it does.
  where
    guardWhitelist (tests : List (String × TestEntry)) :=
      if whitelist.isEmpty then tests else tests.filter (λ (name, _) ↦ name ∈ whitelist)
    guardBlacklist (tests : List (String × TestEntry)) :=
      tests.filter (λ (name, _) ↦ name ∉ GlobalBlacklist ++ blacklist)
    guardCancum (tests : List (String × TestEntry)) :=
      tests.filter (λ (_, test) ↦ test.network.take 6 == "Cancun")

end Conform

end EvmYul
