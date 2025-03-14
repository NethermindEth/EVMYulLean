import Conform.TestRunner
import EvmYul.FFI.ffi

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile : System.FilePath := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile : System.FilePath := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stStackTests/underflowTest.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/Call50000_sha256.json"


def SpecificFile : System.FilePath := "EthereumTests/BlockchainTests/GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/CALLBlake2f.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts/blake2B.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/CALLCODEBlake2f.json"

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")
/--
CannotParse - Missing `postState` entirely.
            - There's a single test that says :intMax or some such before giving an 0x value. What?
-/

private def basicSuccess (name : System.FilePath)
                         (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keys, failed.keys)

def logFile : System.FilePath := "tests.txt"

open EvmYul.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open EvmYul.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) : IO Unit :=
  IO.FS.withFile logFile .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

/-
  Cancun                               :  0m 23s |
  Pyspecs                              :  2m 31s | (1 test failed)
  Shanghai                             :  0m  6s |
  stArgsZeroOneBalance                 :  0m 14s |
  stAttackTest                         :  0m  6s |
  stBadOpcode                          : 10m 42s | 
  stBugs                               :  0m  4s |
  stCallCodes                          :  0m 13s |
  stCallCreateCallCodeTest             :  0m  9s |
  stCallDelegateCodesCallCodeHomestead :  0m 12s |
  stCallDelegateCodesHomestead         :  0m 10s |
  stChainId                            :  0m  3s |
  stCodeCopyTest                       :  0m  3s |
  stCodeSizeLimit                      :  0m  3s |
  stCreate2                            :  5m  5s | 
  stCreateTest                         :  1m  5s |
  stDelegatecallTestHomestead          :  0m 10s |
  stEIP150singleCodeGasPrices          :  1m  5s |
  stEIP150Specific                     :  0m  9s |  
  stEIP158Specific                     :  0m  6s | 
  stEIP1559                            :  4m 30s | (scheduling issue)
  stEIP2930                            :  1m  0s | (scheduling issue)
  stEIP3607                            :  0m  7s |  
  stExample                            :  0m 12s | 
  stExtCodeHash                        :  0m 14s |   
  stHomesteadSpecific                  :  0m  5s |
  stInitCodeTest                       :  0m  6s |   
  stLogTests                           :  0m 11s |   
  stMemExpandingEIP150Calls            :  0m  7s |   
  stMemoryStressTest                   :  0m 12s |   
  stMemoryTest                         :  2m 47s | (scheduling issue)
  stNonZeroCallsTest                   :  0m  8s |   
  stPreCompiledContracts               :  3m 18s |  
  stPreCompiledContracts2              :  0m 28s |   
  stQuadraticComplexityTest            :  1m 42s |   
  stRandom                             :  0m 32s |   
  stRandom2                            :  0m 22s |   
  stRecursiveCreate                    :  0m 37s |  
  stRefundTest                         :  0m  8s |   
  stReturnDataTest                     :  2m  2s |   
  stRevertTest                         :  1m 53s |   
  stSelfBalance                        :  0m 36s |
  stShift                              :  0m  9s |   
  stSLoadTest                          :  0m  5s |     
  stSolidityTest                       :  0m  7s |   
  stSpecialTest                        :  0m  9s |  
  stSStoreTest                         :  0m 35s |   
  stStackTests                         :         |  
  stStaticCall                         :         |   
  stStaticFlagEnabled                  :         | 
  stSystemOperationsTest               :         |   
  stTimeConsuming                      : 11m 42s |
  stTransactionTest                    :         |     
  stTransitionTest                     :         |  
  stWalletTest                         :         |     
  stZeroCallsRevert                    :         |     
  stZeroCallsTest                      :         |     
  stZeroKnowledge                      :         |     
  stZeroKnowledge2                     :         |
  VMTests                                        |

-/

/-
GeneralStateTests:
  Cancun                                2m43

  Pyspecs                               27m47

  Shanghai                              0m42

  stArgsZeroOneBalance                  1m47

  stAttackTest                          0m16

  stBadOpcode                           62m48

  stBugs                                0m23

  stCallCodes                           1m30

  stCallCreateCallCodeTest              1m5

  stCallDelegateCodesCallCodeHomestead  1m5

  stCallDelegateCodesHomestead          1m5

  stChainId                             0m16

  stCodeCopyTest                        0m16

  stCodeSizeLimit                       0m24

  stCreate2                             3m10

  stCreateTest                          3m10

  stDelegatecallTestHomestead           0m48

  stEIP150singleCodeGasPrices           7m15

  stEIP150Specific                      0m38

  stEIP1559                             20m38

  stEIP158Specific                      0m25

  stEIP2930                             2m27

  stEIP3607                             0m27

  stExample                             0m54

  stExtCodeHash                         1m27

  stHomesteadSpecific                   0m19

  stInitCodeTest                        0m37

  stLogTests                            1m2

  stMemExpandingEIP150Calls             0m26

  stMemoryStressTest                    1m32

  stMemoryTest                          10m29

  stNonZeroCallsTest                    0m38

  stPreCompiledContracts                15m21

  stPreCompiledContracts2               56m40

  stQuadraticComplexityTest             6m32

  stRandom                              6m5

  stRandom2                             3m50

  stRecursiveCreate                     0m15

  stRefundTest                          0m43

  stReturnDataTest                      4m56

  stRevertTest                          4m44

  stSelfBalance                         0m58

  stShift                               0m54

  stSLoadTest                           0m15

  stSolidityTest                        0m38

  stSpecialTest                         0m35

  stSStoreTest                          9m10

  stStackTests                          3m53

  stStaticCall                          12m33

  stStaticFlagEnabled                   1m28

  stSystemOperationsTest                1m41

  stTimeConsuming                       81m20

  stTransactionTest                     3m44

  stTransitionTest                      0m20

  stWalletTest                          0m58

  stZeroCallsRevert                     0m29

  stZeroCallsTest                       0m38

  stZeroKnowledge                       24m49

  stZeroKnowledge2                      9m40

  VMTests                               9m16
-/
/-
InvalidBlocks                           2m56
-/
/-
TransitionTests                         1m3
^^^ No Cancun tests here
-/
/-
ValidBlocks                             15m40
-/
def directoryBlacklist : List System.FilePath := []
-- [
--   "EthereumTests/BlockchainTests/GeneralStateTests/VMTests",
--   "EthereumTests/BlockchainTests/GeneralStateTests/stZeroKnowledge",
--   "EthereumTests/BlockchainTests/GeneralStateTests/stTimeConsuming",
--   "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2",
--   "EthereumTests/BlockchainTests/GeneralStateTests/stBadOpcode"
  
--   ]

def fileBlacklist : List System.FilePath := []

def testInput : ByteArray :=
  (ByteArray.ofBlob "0000000048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001").toOption.getD .empty

def testOutput : ByteArray :=
  (ByteArray.ofBlob "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b").toOption.getD .empty

def exampleInput : ByteArray := ⟨#[
  -- rounds (big endian, 4 bytes)
  0, 0, 0, 42,
  -- h (little endian, 8 bytes, 8 times)
  1, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0,
  3, 0, 0, 0, 0, 0, 0, 0,
  4, 0, 0, 0, 0, 0, 0, 0,
  5, 0, 0, 0, 0, 0, 0, 0,
  6, 0, 0, 0, 0, 0, 0, 0,
  7, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 0, 0, 0, 0, 0,
  -- m (little endian, 8 bytes, 16 times)
  1, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0,
  3, 0, 0, 0, 0, 0, 0, 0,
  4, 0, 0, 0, 0, 0, 0, 0,
  5, 0, 0, 0, 0, 0, 0, 0,
  6, 0, 0, 0, 0, 0, 0, 0,
  7, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0,
  3, 0, 0, 0, 0, 0, 0, 0,
  4, 0, 0, 0, 0, 0, 0, 0,
  5, 0, 0, 0, 0, 0, 0, 0,
  6, 0, 0, 0, 0, 0, 0, 0,
  7, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 0, 0, 0, 0, 0,
  -- t (little endian, 8 bytes, 2 times)
  1, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0,
  -- f (1 byte)
  1
]⟩



def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (threads            : ℕ := 1) : IO Unit := do
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

  if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile

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

  dbg_trace s!"Scheduling tests for parallel execution..."
  for (path, names) in testNames do
    for name in names do
      tests := tests.set! thread (tests.get! thread |>.push (path, name))
      thread := thread + 1; thread := thread % threads
  for i in [0:threads] do
    tasks := tasks.push (←IO.asTask <| EvmYul.Conform.processTests i (tests.get! i))

  dbg_trace s!"Scheduled {tests.foldl (· + ·.size) 0} tests on {threads} thread{if threads == 1 then "" else "s"}."
  dbg_trace s!"Running..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for (file, test, res) in batch do
      log file test res
      if res.isNone
      then numSuccess := numSuccess + 1
      else numFailedTest := numFailedTest + 1
  let total := numFailedTest + numSuccess
  IO.println s!"Total tests: {total}"
  IO.println s!"The post was NOT equal to the resulting state: {numFailedTest}"
  IO.println s!"Succeeded: {numSuccess}"
  IO.println s!"Success rate of: {(numSuccess.toFloat / total.toFloat) * 100.0}"

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

  IO.println s!"Phase 1/3 - No performance tests."
  testFiles (root := "EthereumTests/BlockchainTests/")
            (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
            (testBlacklist := DelayFiles)
            (threads := NumThreads)
  
  IO.println s!"Phase 2/3 - Performance tests only."
  testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
            (threads := NumThreads)

  IO.println s!"Phase 3/3 - Individually scheduled tests."
  testFiles (root := "EthereumTests/BlockchainTests/")
            (testWhitelist := DelayFiles)
            (threads := NumThreads)
