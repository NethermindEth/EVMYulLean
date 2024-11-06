import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts/modexp.json"

def TestsSubdir := "BlockchainTests"
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
GeneralStateTests:
  Cancun                                3m37
    Total tests: 187
    The post was NOT equal to the resulting state: 12
    Succeeded: 175
    Success rate of: 93.582888

  Pyspecs                               38m19
    Total tests: 2122
    The post was NOT equal to the resulting state: 434
    Succeeded: 1688
    Success rate of: 79.547597

  Shanghai                              0m42
    Total tests: 27
    The post was NOT equal to the resulting state: 6
    Succeeded: 21
    Success rate of: 77.777778

  stArgsZeroOneBalance                  1m47
    Total tests: 96
    The post was NOT equal to the resulting state: 0
    Succeeded: 96
    Success rate of: 100.000000

  stAttackTest                          0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 2
    Succeeded: 0
    Success rate of: 0.000000

  stBadOpcode                           75m51
    Total tests: 4249
    The post was NOT equal to the resulting state: 574
    Succeeded: 3675
    Success rate of: 86.490939

  stBugs                                0m23
    Total tests: 9
    The post was NOT equal to the resulting state: 0
    Succeeded: 9
    Success rate of: 100.000000

  stCallCodes                           -

  stCallCreateCallCodeTest              1m5
    Total tests: 55
    The post was NOT equal to the resulting state: 8
    Succeeded: 47
    Success rate of: 85.454545

  stCallDelegateCodesCallCodeHomestead  -

  stCallDelegateCodesHomestead          -

  stChainId                             0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 0
    Succeeded: 2
    Success rate of: 100.000000

  stCodeCopyTest                        0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 0
    Succeeded: 2
    Success rate of: 100.000000

  stCodeSizeLimit                       0m23
    Total tests: 9
    The post was NOT equal to the resulting state: 1
    Succeeded: 8
    Success rate of: 88.888889

  stCreate2                             3m10
    Total tests: 183
    The post was NOT equal to the resulting state: 47
    Succeeded: 136
    Success rate of: 74.316940

  stCreateTest                          3m10
    Total tests: 196
    The post was NOT equal to the resulting state: 80
    Succeeded: 116
    Success rate of: 59.183673

  stDelegatecallTestHomestead           0m52
    Total tests: 33
    The post was NOT equal to the resulting state: 6
    Succeeded: 27
    Success rate of: 81.818182

  stEIP150singleCodeGasPrices           7m15
    Total tests: 450
    The post was NOT equal to the resulting state: 49
    Succeeded: 401
    Success rate of: 89.111111

  stEIP150Specific                      0m38
    Total tests: 450
    The post was NOT equal to the resulting state: 49
    Succeeded: 401
    Success rate of: 89.111111

  stEIP1559                             26m52
    Total tests: 1845
    The post was NOT equal to the resulting state: 238
    Succeeded: 1607
    Success rate of: 87.100271

  stEIP158Specific                      0m22
    Total tests: 8
    The post was NOT equal to the resulting state: 5
    Succeeded: 3
    Success rate of: 37.500000

  stEIP2930                             1m50
    Total tests: 140
    The post was NOT equal to the resulting state: 120
    Succeeded: 20
    Success rate of: 14.285714

  stEIP3607                             0m27
    Total tests: 12
    The post was NOT equal to the resulting state: 0
    Succeeded: 12
    Success rate of: 100.000000

  stExample                             0m53
    Total tests: 39
    The post was NOT equal to the resulting state: 6
    Succeeded: 33
    Success rate of: 84.615385

  stExtCodeHash                         1m20
    Total tests: 69
    The post was NOT equal to the resulting state: 52
    Succeeded: 17
    Success rate of: 24.637681

  stHomesteadSpecific                   0m19
    Total tests: 5
    The post was NOT equal to the resulting state: 2
    Succeeded: 3
    Success rate of: 60.000000

  stInitCodeTest                        0m37
    Total tests: 22
    The post was NOT equal to the resulting state: 2
    Succeeded: 20
    Success rate of: 90.909091

  stLogTests                            1m2
    Total tests: 46
    The post was NOT equal to the resulting state: 5
    Succeeded: 41
    Success rate of: 89.130435

  stMemExpandingEIP150Calls             0m26
    Total tests: 14
    The post was NOT equal to the resulting state: 6
    Succeeded: 8
    Success rate of: 57.142857

  stMemoryStressTest                    2m46
    Total tests: 82
    The post was NOT equal to the resulting state: 3
    Succeeded: 79
    Success rate of: 96.341463

  stMemoryTest                          10m29
    Total tests: 561
    The post was NOT equal to the resulting state: 79
    Succeeded: 482
    Success rate of: 85.918004

  stNonZeroCallsTest                    0m38
    Total tests: 24
    The post was NOT equal to the resulting state: 8
    Succeeded: 16
    Success rate of: 66.666667

  stPreCompiledContracts                15m21
    Total tests: 894
    The post was NOT equal to the resulting state: 67
    Succeeded: 827
    Success rate of: 92.505593

  stPreCompiledContracts2               56m40
    Total tests: 226
    The post was NOT equal to the resulting state: 36
    Succeeded: 190
    Success rate of: 84.070796

  stQuadraticComplexityTest             6m32
    Total tests: 32
    The post was NOT equal to the resulting state: 10
    Succeeded: 22
    Success rate of: 68.750000

  stRandom                              6m5
    Total tests: 308
    The post was NOT equal to the resulting state: 6
    Succeeded: 302
    Success rate of: 98.051948

  stRandom2                             3m50
    Total tests: 218
    The post was NOT equal to the resulting state: 6
    Succeeded: 212
    Success rate of: 97.247706

  stRecursiveCreate                     0m15
    Total tests: 1
    The post was NOT equal to the resulting state: 1
    Succeeded: 0
    Success rate of: 0.000000

  stRefundTest                          0m40
    Total tests: 26
    The post was NOT equal to the resulting state: 5
    Succeeded: 21
    Success rate of: 80.769231

  stReturnDataTest                      4m56
    Total tests: 269
    The post was NOT equal to the resulting state: 12
    Succeeded: 257
    Success rate of: 95.539033

  stRevertTest                          4m44
    Total tests: 233
    The post was NOT equal to the resulting state: 23
    Succeeded: 210
    Success rate of: 90.128755

  stSelfBalance                         0m58
    Total tests: 42
    The post was NOT equal to the resulting state: 1
    Succeeded: 41
    Success rate of: 97.619048

  stShift                               0m54
    Total tests: 42
    The post was NOT equal to the resulting state: 2
    Succeeded: 40
    Success rate of: 95.238095

  stSLoadTest                           0m15
    Total tests: 1
    The post was NOT equal to the resulting state: 0
    Succeeded: 1
    Success rate of: 100.000000

  stSolidityTest                        0m38
    Total tests: 23
    The post was NOT equal to the resulting state: 9
    Succeeded: 14
    Success rate of: 60.869565

  stSpecialTest                         0m35
    Total tests: 20
    The post was NOT equal to the resulting state: 6
    Succeeded: 14
    Success rate of: 70.000000

  stSStoreTest                          9m10
    Total tests: 475
    The post was NOT equal to the resulting state: 116
    Succeeded: 359
    Success rate of: 75.578947

  stStackTests                          3m53
    Total tests: 209
    The post was NOT equal to the resulting state: 1
    Succeeded: 208
    Success rate of: 99.521531

  stStaticCall                          15m39
    Total tests: 468
    The post was NOT equal to the resulting state: 55
    Succeeded: 413
    Success rate of: 88.247863

  stStaticFlagEnabled                   0m46
    Total tests: 34
    The post was NOT equal to the resulting state: 9
    Succeeded: 25
    Success rate of: 73.529412

  stSystemOperationsTest                1m41
    Total tests: 83
    The post was NOT equal to the resulting state: 14
    Succeeded: 69
    Success rate of: 83.132530

  stTimeConsuming                       81m20
    Total tests: 5190
    The post was NOT equal to the resulting state: 2
    Succeeded: 5188
    Success rate of: 99.961464

  stTransactionTest                     3m44
    Total tests: 259
    The post was NOT equal to the resulting state: 34
    Succeeded: 225
    Success rate of: 86.872587

  stTransitionTest                      0m20
    Total tests: 6
    The post was NOT equal to the resulting state: 0
    Succeeded: 6
    Success rate of: 100.000000

  stWalletTest                          0m58
    Total tests: 41
    The post was NOT equal to the resulting state: 0
    Succeeded: 41
    Success rate of: 100.000000

  stZeroCallsRevert                     0m29
    Total tests: 16
    The post was NOT equal to the resulting state: 0
    Succeeded: 16
    Success rate of: 100.000000

  stZeroCallsTest                       0m38
    Total tests: 24
    The post was NOT equal to the resulting state: 12
    Succeeded: 12
    Success rate of: 50.000000

  stZeroKnowledge                       13m15
    Total tests: 944
    The post was NOT equal to the resulting state: 411
    Succeeded: 533
    Success rate of: 56.461864

  stZeroKnowledge2                      9m40
    Total tests: 519
    The post was NOT equal to the resulting state: 170
    Succeeded: 349
    Success rate of: 67.244701

  VMTests                               9m16
    Total tests: 571
    The post was NOT equal to the resulting state: 25
    Succeeded: 546
    Success rate of: 95.621716
-/
/-
InvalidBlocks                           2m56
  Total tests: 126
  The post was NOT equal to the resulting state: 4
  Succeeded: 122
  Success rate of: 96.825397
-/
/-
TransitionTests                         1m3
  Total tests: 17
  The post was NOT equal to the resulting state: 11
  Succeeded: 6
  Success rate of: 35.294118
-/
/-
ValidBlocks                             15m40
  Total tests: 437
  The post was NOT equal to the resulting state: 112
  Succeeded: 325
  Success rate of: 74.370709
-/
def directoryBlacklist : List System.FilePath :=
  [ "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes" -- 86 tests
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallDelegateCodesCallCodeHomestead" -- 58 tests
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallDelegateCodesHomestead" -- 58 tests
  ]
#check 0x03e8
def fileBlacklist : List System.FilePath :=
  [ "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_25000.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_20500.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexpRandomInput.json" -- 6
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_35000.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_22000.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stRevertTest/RevertPrecompiledTouch_nonce.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stRevertTest/RevertPrecompiledTouch_noncestorage.json" -- 4
  , "EthereumTests/BlockchainTests/GeneralStateTests/stRevertTest/RevertPrecompiledTouch_storage_Paris.json" -- 4
  ]
#eval 19098.0 / (22265 + 425)
#eval 475.0 / 60
-- Total tests: 1071
-- The post was NOT equal to the resulting state: 179
-- Succeeded: 892
-- Success rate of: 83.286648

def main : IO Unit := do
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
        -- ("EthereumTests/BlockchainTests")
        ("EthereumTests/BlockchainTests")

  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  let testFiles := #[SpecificFile]

  let mut discardedFiles := #[]

  let mut numFailedTest := 0
  let mut numSuccess := 0

  if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile

  for testFile in testFiles do
    if fileBlacklist.contains testFile then continue
    dbg_trace s!"File under test: {testFile}"
    let res ←
      ExceptT.run <|
        EvmYul.Conform.processTestsOfFile
          (whitelist := #[
            "modexp_d29g0v0_Cancun"
          , "modexp_d29g1v0_Cancun"
          , "modexp_d29g2v0_Cancun"
          , "modexp_d29g3v0_Cancun"
          ])
          -- (whitelist := #["add_d4g0v0_Cancun"])
          testFile
    match res with
      | .error err         => discardedFiles := discardedFiles.push (testFile, err)
      | .ok    testresults => for (test, result) in testresults do
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
