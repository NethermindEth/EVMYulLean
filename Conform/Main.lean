import Conform.TestRunner
import EvmYul.FFI.ffi

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

#check Task

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
  Threads are scheduled on per-file basis. This granularity is not sufficient.

  Cancun                               :  0m 40s | 16threads
  Pyspecs                              :  3m  8s | 16threads (1 test failed)
  Shanghai                             :  0m  6s |  8threads
  stArgsZeroOneBalance                 :  0m 14s | 16threads
  stAttackTest                         :  0m  6s |  2threads
  stBadOpcode                          : 14m 19s | 16threads (scheduling not ideal, need per-testcase)
  stBugs                               :  0m  4s |  5threads
  stCallCodes                          :  0m 13s | 16threads
  stCallCreateCallCodeTest             :  0m  9s | 16threads
  stCallDelegateCodesCallCodeHomestead :  0m 12s | 16threads
  stCallDelegateCodesHomestead         :  0m 10s | 16threads
  stChainId                            :  0m  3s |  2threads
  stCodeCopyTest                       :  0m  3s |  2threads
  stCodeSizeLimit                      :  0m  3s |  5threads
  stCreate2                            :  5m  5s | 16threads (_all_ slow tests in Create2Recursive, scheduled for a single thread, ouch)
  stCreateTest                         :  1m  5s | 16threads
  stDelegatecallTestHomestead          :  0m 10s | 16threads
  stEIP150singleCodeGasPrices          :  1m  5s | 16threads
  stEIP150Specific                     :  0m  9s | 14threads  
  stEIP158Specific                     :  0m  6s |  8threads 
  stEIP1559                            :  4m 30s | 13threads (scheduling issue)
  stEIP2930                            :  1m  0s |  7threads (scheduling issue)
  stEIP3607                            :  0m  7s |  5threads  
  stExample                            :  0m 12s | 12threads 
  stExtCodeHash                        :  0m 14s | 16threads   
  stHomesteadSpecific                  :  0m  5s |  5threads
  stInitCodeTest                       :  0m  6s | 16threads   
  stLogTests                           :  0m 11s | 16threads   
  stMemExpandingEIP150Calls            :  0m  7s |  9threads   
  stMemoryStressTest                   :  0m 12s | 16threads   
  stMemoryTest                         :  2m 47s | 16threads (scheduling issue)
  stNonZeroCallsTest                   :  0m  8s | 16threads   
  stPreCompiledContracts               :  3m 18s |  9threads  
  stPreCompiledContracts2              :  0m 28s | 16threads   
  stQuadraticComplexityTest            :  1m 42s | 16threads   
  stRandom                             :  0m 32s | 16threads   
  stRandom2                            :  0m 22s | 16threads   
  stRecursiveCreate                    :  0m 37s |  2threads  
  stRefundTest                         :  0m  8s | 16threads   
  stReturnDataTest                     :  2m  2s | 16threads   
  stRevertTest                         :  1m 53s | 16threads   
  stSelfBalance                        :  0m 36s |  6threads
  stShift                              :  0m  9s | 16threads   
  stSLoadTest                          :  0m  5s |  1thread     
  stSolidityTest                       :  0m  7s | 16threads   
  stSpecialTest                        :  0m  9s | 15threads  
  stSStoreTest                         :  0m 35s | 16threads   
  stStackTests                         :         | 10threads  
  stStaticCall                         :         | 16threads   
  stStaticFlagEnabled                  :         | 13threads 
  stSystemOperationsTest               :         | 16threads   
  stTimeConsuming                      : 11m 42s | 14threads
  stTransactionTest                    :         | 16threads     
  stTransitionTest                     :         |  6threads  
  stWalletTest                         :         | 16threads     
  stZeroCallsRevert                    :         | 16threads     
  stZeroCallsTest                      :         | 16threads     
  stZeroKnowledge                      :         | 16threads     
  stZeroKnowledge2                     :         | 16threads
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

def main (args : List String) : IO Unit := do
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD 1
  dbg_trace s!"Running tests on {NumThreads} thread{if NumThreads == 1 then "" else "s"}."
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
        -- ("EthereumTests/BlockchainTests")
        -- ("EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts")
        -- ("EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance")
        -- ("EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs")
        -- ("EthereumTests/BlockchainTests/GeneralStateTests/Shanghai")
        ("EthereumTests/BlockchainTests/GeneralStateTests/Cancun")
        -- ("EthereumTests/BlockchainTests/GeneralStateTests/stTimeConsuming")
  let mut discardedFiles : Array System.FilePath := #[]
  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]
  -- let testFiles : Array System.FilePath := #["EthereumTests/BlockchainTests/GeneralStateTests/stZeroCallsTest/ZeroValue_CALLCODE_ToEmpty_Paris.json"]
  let testFiles : Array System.FilePath := #["EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/loopMul.json"]

  let mut numFailedTest := 0
  let mut numSuccess := 0

  let testFiles := testFiles.filter (· ∉ fileBlacklist)
  let NumChunks := testFiles.size / NumThreads
  let mut numRemaining := testFiles.size % NumThreads
  dbg_trace s!"Running {testFiles.size} files; {NumChunks} per thread."
  
  if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile
  -- dbg_trace s!"test files: {testFiles}"
  let mut tasks : Array (Task _) := .empty
  for thread in [0:NumThreads] do
    let mut files : Array System.FilePath := .empty
    for offset in [0:NumChunks] do
      let testFileIdx := thread * NumChunks + offset
      files := files.push testFiles[testFileIdx]!
    if 0 < numRemaining then
      dbg_trace s!"huh: {NumThreads * NumChunks + numRemaining} numRemaining: {numRemaining}"
      numRemaining := numRemaining - 1
      files := files.push testFiles[NumThreads * NumChunks + numRemaining]!
    dbg_trace s!"Batching: {files} on thread: {thread}."
    tasks := tasks.push (←IO.asTask (EvmYul.Conform.processTestsOfFiles thread (whitelist := #["loopMul_d0g0v0_Cancun"]) files))
  dbg_trace s!"Patience is a virtue..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for (testresults, testFile) in batch do
      for (test, result) in testresults do
        -- dbg_trace "ok! - testresults: {repr testresults}"
        -- dbg_trace s!"test: {test} result: {result}"
        log testFile test result
        if result.isNone
        then numSuccess := numSuccess + 1
        else numFailedTest := numFailedTest + 1
  let total := numFailedTest + numSuccess
  IO.println s!"Total tests: {total}"
  IO.println s!"The post was NOT equal to the resulting state: {numFailedTest}"
  IO.println s!"Succeeded: {numSuccess}"
  IO.println s!"Success rate of: {(numSuccess.toFloat / total.toFloat) * 100.0}"

  IO.println s!"Files discarded along the way: {repr discardedFiles}"
  -- let gatherMaps := testResults.map
  --   (λ εmaps ↦ εmaps.map
  --     (λ maps ↦ maps.foldl
  --       (init := Batteries.RBMap.empty)
  --       (Batteries.RBMap.mergeWith (λ _ _ m ↦ dbg_trace "Nonunique test name."; m))))
  -- for εmap in testResults do
  --   match εmap with
  --     | .error err         => dbg_trace "error!"
  --                             discardedFiles := discardedFiles.push (err.toFilePath, err)
  --     | .ok    testresults => for (results, testFile) in testresults do
  --                               dbg_trace "ok! - testresults: {repr testresults}"
  --                               for (test, result) in testresults do
  --                                 dbg_trace s!"test: {test} result: {result}"
  --                                 log testFile test result
  --                                 if result.isNone
  --                                 then numSuccess := numSuccess + 1
  --                                 else numFailedTest := numFailedTest + 1
  -- gatherMaps.map _

  

    -- testResults.push (IO.ofExcept (← IO.wait task))

  -- mergeWith

    -- -- if fileBlacklist.contains testFile then continue
    --   let res ←
    --     ExceptT.run <|
    --       EvmYul.Conform.processTestsOfFile
    --         (whitelist :=
    --           #[ -- "CALLBlake2f_d1g0v0_Cancun"
    --           --   "21_tstoreCannotBeDosdOOO_d0g0v0_Cancun"
    --           -- , "15_tstoreCannotBeDosd_d0g0v0_Cancun"
    --           -- , "ContractCreationSpam_d0g0v0_Cancun"
    --           -- , "static_Return50000_2_d0g0v0_Cancun"
    --           -- , "static_Call50000_identity_d0g0v0_Cancun"
    --           -- , "static_Call50000_identity_d1g0v0_Cancun"
    --           -- , "static_Call50000_ecrec_d0g0v0_Cancun"
    --           -- , "static_Call50000_ecrec_d0g0v0_Cancun"
    --           -- , "static_Call50000_identity2_d0g0v0_Cancun"
    --           -- , "static_Call50000_identity2_d1g0v0_Cancun"
    --           -- , "static_LoopCallsThenRevert_d0g0v0_Cancun"
    --           -- , "static_LoopCallsThenRevert_d0g1v0_Cancun"
    --           -- , "static_Call50000_d0g0v0_Cancun"
    --           -- , "static_Call50000_d1g0v0_Cancun"
    --           -- , "static_Call50000_rip160_d0g0v0_Cancun"
    --           -- , "static_Call50000_rip160_d1g0v0_Cancun"
    --           -- , "loopMul_d0g0v0_Cancun" -- OOF
    --           -- , "loopMul_d1g0v0_Cancun" -- OOF
    --           -- , "loopMul_d2g0v0_Cancun" -- OOF
    --           -- , "performanceTester_d1g0v0_Cancun"
    --           -- , "performanceTester_d4g0v0_Cancun"
    --           -- , "loopExp_d10g0v0_Cancun" -- OOF
    --           -- , "loopExp_d11g0v0_Cancun" -- OOF
    --           -- , "loopExp_d12g0v0_Cancun" -- OOF
    --           -- , "loopExp_d13g0v0_Cancun"
    --           -- , "loopExp_d14g0v0_Cancun" -- OOF
    --           -- , "loopExp_d8g0v0_Cancun" -- OOF
    --           -- , "loopExp_d9g0v0_Cancun" -- OOF
    --           -- , "Return50000_2_d0g0v0_Cancun"
    --           -- , "Call50000_identity2_d0g1v0_Cancun"
    --           -- , "Call50000_ecrec_d0g1v0_Cancun"
    --           -- , "Return50000_d0g1v0_Cancun"
    --           -- ,
    --           -- "Call50000_sha256_d0g1v0_Cancun"
    --           -- , "Call50000_d0g1v0_Cancun"
    --           -- , "Callcode50000_d0g1v0_Cancun"
    --           -- , "Call50000_identity_d0g1v0_Cancun"
    --           -- , "QuadraticComplexitySolidity_CallDataCopy_d0g1v0_Cancun"
    --           -- , "static_Call50000_sha256_d0g0v0_Cancun"
    --           -- , "static_Call50000_sha256_d1g0v0_Cancun"
    --           "CALLBlake2f_MaxRounds_d0g0v0_Cancun"
    --           ]
    --         )

    --       testFile
    -- Except EvmYul.Conform.Exception (Batteries.RBMap String EvmYul.Conform.TestResult compare)
  --   for res in gatherMaps do
  --   match res with
  --     | .error err         => dbg_trace "error!"
  --                             discardedFiles := discardedFiles.push (testFile, err)
  --     | .ok    testresults => dbg_trace "ok! - testresults: {repr testresults}"
  --                             for (test, result) in testresults do
  --                               dbg_trace s!"test: {test} result: {result}"
  --                               log testFile test result
  --                               if result.isNone
  --                               then numSuccess := numSuccess + 1
  --                               else numFailedTest := numFailedTest + 1

  -- let total := numFailedTest + numSuccess
  -- IO.println s!"Total tests: {total}"
  -- IO.println s!"The post was NOT equal to the resulting state: {numFailedTest}"
  -- IO.println s!"Succeeded: {numSuccess}"
  -- IO.println s!"Success rate of: {(numSuccess.toFloat / total.toFloat) * 100.0}"

  -- IO.println s!"Files discarded along the way: {repr discardedFiles}"
