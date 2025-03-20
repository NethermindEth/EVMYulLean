import Conform.TestRunner
import EvmYul.FFI.ffi

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

private def basicSuccess (name : System.FilePath)
                         (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keys, failed.keys)

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open EvmYul.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open EvmYul.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false) : IO (Nat × Nat) := do
  let isToBeTested (testname : String) : Bool :=
    let whitelist := testWhitelist
    let blacklist := testBlacklist ++ EvmYul.Conform.GlobalBlacklist
    testname ∉ blacklist ∧ (whitelist.isEmpty ∨ testname ∈ whitelist)

  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir root (pure <| · ∉ directoryBlacklist)

  let testFiles := testFiles.filter (· ∉ fileBlacklist)

  let mut discardedFiles : Array (System.FilePath × String) := #[]
  let mut numFailedTest := 0
  let mut numSuccess := 0

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  let testJsons ← testFiles.mapM Lean.Json.fromFile
  let testNames : Array (System.FilePath × Array String) :=
    testJsons.zip testFiles |>.map
      λ (json, filepath) ↦
        match json.getObj? with
        | .error _ => panic! "Malformed test json."
        | .ok x => (filepath, x.toArray.map Sigma.fst |>.filter isToBeTested)  

  let mut tasks : Array (Task _) := .empty
  let mut thread := 0
  let mut tests : Array (Array (System.FilePath × String)) := .mkArray threads #[]

  IO.println s!"Scheduling tests for parallel execution..."
  for (path, names) in testNames do
    for name in names do
      tests := tests.set! thread (tests.get! thread |>.push (path, name))
      thread := thread + 1; thread := thread % threads
  for i in [0:threads] do
    tasks := tasks.push (←IO.asTask <| EvmYul.Conform.processTests (tests.get! i) (if timed then .some i else .none))

  IO.println s!"Scheduled {tests.foldl (· + ·.size) 0} tests on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res) in batch do
      log file test res phase
      if res.isNone
      then numSuccess := numSuccess + 1
      else numFailedTest := numFailedTest + 1
  return (numSuccess, numFailedTest)

def main (args : List String) : IO Unit := do
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD 1

  let DelayFiles : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun",
      "SuicideIssue_Cancun"]

  let printResults (result : ℕ × ℕ) : IO Unit := do
    let (success, failure) := result
    IO.println s!"Total tests: {success + failure}"
    IO.println s!"The post was NOT equal to the resulting state: {failure}"
    IO.println s!"Succeeded: {success}"
    IO.println s!"Success rate of: {(success.toFloat / (failure + success).toFloat) * 100.0}"

  IO.println s!"Phase 1/3 - No performance tests."
  testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/Cancun")
            (phase := 1)
            (threads := NumThreads) 
            (timed := true) >>= printResults

  -- IO.println s!"Phase 1/3 - No performance tests."
  -- testFiles (root := "EthereumTests/BlockchainTests/")
  --           (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
  --           (testBlacklist := DelayFiles)
  --           (phase := 1)
  --           (threads := NumThreads) >>= printResults
  
  -- IO.println s!"Phase 2/3 - Performance tests only."
  -- testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
  --           (phase := 2)
  --           (threads := NumThreads) >>= printResults

  -- IO.println s!"Phase 3/3 - Individually scheduled tests."
  -- testFiles (root := "EthereumTests/BlockchainTests/")
  --           (testWhitelist := DelayFiles)
  --           (phase := 3)
  --           (threads := NumThreads) >>= printResults
