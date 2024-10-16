import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stCreateTest/CREATE_ContractRETURNBigOffset.json"

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
  Cancun                                2m59
    Total tests: 189
    The post was NOT equal to the resulting state: 73
    Succeeded: 116
    Success rate of: 61.375661

  Pyspecs                               17m54
    Total tests: 2150
    The post was NOT equal to the resulting state: 1779
    Succeeded: 371
    Success rate of: 17.255814

  Shanghai                              0m42
    Total tests: 27
    The post was NOT equal to the resulting state: 23
    Succeeded: 4
    Success rate of: 14.814815

  stArgsZeroOneBalance                  1m47
    Total tests: 96
    The post was NOT equal to the resulting state: 6
    Succeeded: 90
    Success rate of: 93.750000

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
    The post was NOT equal to the resulting state: 2
    Succeeded: 7
    Success rate of: 77.777778

  stCallCodes                           -

  stCallCreateCallCodeTest              1m5
    Total tests: 55
    The post was NOT equal to the resulting state: 22
    Succeeded: 33
    Success rate of: 60.000000

  stCallDelegateCodesCallCodeHomestead  -

  stCallDelegateCodesHomestead          -

  stChainId                             0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 0
    Succeeded: 2
    Success rate of: 100.000000

  stCodeCopyTest                        0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 1
    Succeeded: 1
    Success rate of: 50.000000

  stCodeSizeLimit                       0m23
    Total tests: 9
    The post was NOT equal to the resulting state: 1
    Succeeded: 8
    Success rate of: 88.888889

  stCreate2                             3m10
    Total tests: 183
    The post was NOT equal to the resulting state: 76
    Succeeded: 107
    Success rate of: 58.469945

  stCreateTest                          3m10
    Total tests: 196
    The post was NOT equal to the resulting state: 107
    Succeeded: 89
    Success rate of: 45.408163

  stDelegatecallTestHomestead           0m52
    Total tests: 33
    The post was NOT equal to the resulting state: 26
    Succeeded: 7
    Success rate of: 21.212121

  stEIP150singleCodeGasPrices           8m11
    Total tests: 450
    The post was NOT equal to the resulting state: 336
    Succeeded: 114
    Success rate of: 25.333333

  stEIP150Specific                      0m38
    Total tests: 23
    The post was NOT equal to the resulting state: 19
    Succeeded: 4
    Success rate of: 17.391304

  stEIP1559                             17m16
    Total tests: 1845
    The post was NOT equal to the resulting state: 926
    Succeeded: 919
    Success rate of: 49.810298

  stEIP158Specific                      0m22
    Total tests: 8
    The post was NOT equal to the resulting state: 7
    Succeeded: 1
    Success rate of: 12.500000

  stEIP2930                             1m34
    Total tests: 140
    The post was NOT equal to the resulting state: 139
    Succeeded: 1
    Success rate of: 0.714286

  stEIP3607                             0m27
    Total tests: 12
    The post was NOT equal to the resulting state: 0
    Succeeded: 12
    Success rate of: 100.000000

  stExample                             0m53
    Total tests: 39
    The post was NOT equal to the resulting state: 35
    Succeeded: 4
    Success rate of: 10.256410

  stExtCodeHash                         1m20
    Total tests: 69
    The post was NOT equal to the resulting state: 66
    Succeeded: 3
    Success rate of: 4.347826

  stHomesteadSpecific                   0m19
    Total tests: 5
    The post was NOT equal to the resulting state: 2
    Succeeded: 3
    Success rate of: 60.000000

  stInitCodeTest                        0m37
    Total tests: 22
    The post was NOT equal to the resulting state: 16
    Succeeded: 6
    Success rate of: 27.272727

  stLogTests                            1m2
    Total tests: 46
    The post was NOT equal to the resulting state: 20
    Succeeded: 26
    Success rate of: 56.521739

  stMemExpandingEIP150Calls             0m26
    Total tests: 14
    The post was NOT equal to the resulting state: 13
    Succeeded: 1
    Success rate of: 7.142857

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
    The post was NOT equal to the resulting state: 14
    Succeeded: 10
    Success rate of: 41.666667

  stPreCompiledContracts                14m47
    Total tests: 950
    The post was NOT equal to the resulting state: 758
    Succeeded: 192
    Success rate of: 20.210526

  stPreCompiledContracts2               29m18
    Total tests: 226
    The post was NOT equal to the resulting state: 204
    Succeeded: 22
    Success rate of: 9.734513

  stQuadraticComplexityTest             0m41
    Total tests: 32
    The post was NOT equal to the resulting state: 26
    Succeeded: 6
    Success rate of: 18.750000

  stRandom                              6m5
    Total tests: 308
    The post was NOT equal to the resulting state: 54
    Succeeded: 254
    Success rate of: 82.467532

  stRandom2                             4m1
    Total tests: 219
    The post was NOT equal to the resulting state: 13
    Succeeded: 206
    Success rate of: 94.063927

  stRecursiveCreate                     0m15
    Total tests: 1
    The post was NOT equal to the resulting state: 1
    Succeeded: 0
    Success rate of: 0.000000

  stRefundTest                          0m40
    Total tests: 26
    The post was NOT equal to the resulting state: 10
    Succeeded: 16
    Success rate of: 61.538462

  stReturnDataTest                      4m56
    Total tests: 273
    The post was NOT equal to the resulting state: 44
    Succeeded: 229
    Success rate of: 83.882784

  stRevertTest                          4m44
    Total tests: 262
    The post was NOT equal to the resulting state: 57
    Succeeded: 205
    Success rate of: 78.244275

  stSelfBalance                         0m58
    Total tests: 42
    The post was NOT equal to the resulting state: 39
    Succeeded: 3
    Success rate of: 7.142857

  stShift                               0m59
    Total tests: 42
    The post was NOT equal to the resulting state: 10
    Succeeded: 32
    Success rate of: 76.190476

  stSLoadTest                           0m15
    Total tests: 1
    The post was NOT equal to the resulting state: 0
    Succeeded: 1
    Success rate of: 100.000000

  stSolidityTest                        0m38
    Total tests: 23
    The post was NOT equal to the resulting state: 16
    Succeeded: 7
    Success rate of: 30.434783

  stSpecialTest                         0m35
    Total tests: 21
    The post was NOT equal to the resulting state: 11
    Succeeded: 10
    Success rate of: 47.619048

  stSStoreTest                          9m10
    Total tests: 475
    The post was NOT equal to the resulting state: 116
    Succeeded: 359
    Success rate of: 75.578947

  stStackTests                          3m53
    Total tests: 209
    The post was NOT equal to the resulting state: 144
    Succeeded: 65
    Success rate of: 31.100478

  stStaticCall                          7m56
    Total tests: 469
    The post was NOT equal to the resulting state: 397
    Succeeded: 72
    Success rate of: 15.351812

  stStaticFlagEnabled                   0m46
    Total tests: 34
    The post was NOT equal to the resulting state: 34
    Succeeded: 0
    Success rate of: 0.000000

  stSystemOperationsTest                1m41
    Total tests: 83
    The post was NOT equal to the resulting state: 50
    Succeeded: 33
    Success rate of: 39.759036

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
    The post was NOT equal to the resulting state: 3
    Succeeded: 3
    Success rate of: 50.000000

  stWalletTest                          0m58
    Total tests: 41
    The post was NOT equal to the resulting state: 30
    Succeeded: 11
    Success rate of: 26.829268

  stZeroCallsRevert                     0m29
    Total tests: 16
    The post was NOT equal to the resulting state: 3
    Succeeded: 13
    Success rate of: 81.250000

  stZeroCallsTest                       0m38
    Total tests: 24
    The post was NOT equal to the resulting state: 14
    Succeeded: 10
    Success rate of: 41.666667

  stZeroKnowledge                       13m15
    Total tests: 944
    The post was NOT equal to the resulting state: 568
    Succeeded: 376
    Success rate of: 39.830508

  stZeroKnowledge2                      9m40
    Total tests: 519
    The post was NOT equal to the resulting state: 170
    Succeeded: 349
    Success rate of: 67.244701

  VMTests                               9m16
    Total tests: 571
    The post was NOT equal to the resulting state: 31
    Succeeded: 540
    Success rate of: 94.570928
-/
/-
InvalidBlocks 2m56
  Total tests: 126
  The post was NOT equal to the resulting state: 98
  Succeeded: 28
  Success rate of: 22.222222
-/
/-
TransitionTests
  Total tests: 17
  The post was NOT equal to the resulting state: 17
  Succeeded: 0
  Success rate of: 0.000000
-/
/-
ValidBlocks
  Total tests: 437
  The post was NOT equal to the resulting state: 215
  Succeeded: 222
  Success rate of: 50.800915
-/
def directoryBlacklist : List System.FilePath :=
  [ "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes" -- 86 tests
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallDelegateCodesCallCodeHomestead" -- 58 tests
  ]

def fileBlacklist : List System.FilePath :=
  [ "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_25000.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_20500.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexpRandomInput.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_35000.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2/modexp_0_0_0_22000.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stRevertTest/RevertPrecompiledTouchExactOOG_Paris.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes/callcodecallcall_100_OOGMBefore.json"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes/callcodecallcodecallcode_111_OOGMBefore.json"
  ]

def main : IO Unit := do
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
        ("EthereumTests/BlockchainTests")

  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]

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
          -- (whitelist := #["opc2FDiffPlaces_d24g0v0_Cancun"])
          -- (whitelist := #["add_d1g0v0_Cancun"])
          -- (whitelist := #["add_d3g0v0_Cancun"])
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
