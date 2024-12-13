import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stCreate2/RevertOpcodeInCreateReturnsCreate2.json"

def TestsSubdir := "BlockchainTests"
def isTestFile (file : System.FilePath  ) : Bool := file.extension.option false (· == "json")
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
  Cancun                                2m43
    Total tests: 174
    The post was NOT equal to the resulting state: 8
    Succeeded: 166
    Success rate of: 95.402299

  Pyspecs                               27m47
    Total tests: 1675
    The post was NOT equal to the resulting state: 41
    Succeeded: 1634
    Success rate of: 97.552239

  Shanghai                              0m42
    Total tests: 27
    The post was NOT equal to the resulting state: 0
    Succeeded: 27
    Success rate of: 100.000000

  stArgsZeroOneBalance                  1m47
    Total tests: 96
    The post was NOT equal to the resulting state: 0
    Succeeded: 96
    Success rate of: 100.000000

  stAttackTest                          0m16
    Total tests: 2
    The post was NOT equal to the resulting state: 1
    Succeeded: 1
    Success rate of: 50.000000

  stBadOpcode                           62m48
    Total tests: 4132
    The post was NOT equal to the resulting state: 138
    Succeeded: 3994
    Success rate of: 96.660213

  stBugs                                0m23
    Total tests: 8
    The post was NOT equal to the resulting state: 0
    Succeeded: 8
    Success rate of: 100.000000

  stCallCodes                           1m30
    Total tests: 86
    The post was NOT equal to the resulting state: 0
    Succeeded: 86
    Success rate of: 100.000000

  stCallCreateCallCodeTest              1m5
    Total tests: 56
    The post was NOT equal to the resulting state: 5
    Succeeded: 51
    Success rate of: 91.071429

  stCallDelegateCodesCallCodeHomestead  1m5
    Total tests: 58
    The post was NOT equal to the resulting state: 0
    Succeeded: 58
    Success rate of: 100.000000

  stCallDelegateCodesHomestead          1m5
    Total tests: 58
    The post was NOT equal to the resulting state: 0
    Succeeded: 58
    Success rate of: 100.000000

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

  stCodeSizeLimit                       0m24
    Total tests: 9
    The post was NOT equal to the resulting state: 0
    Succeeded: 9
    Success rate of: 100.000000

  stCreate2                             3m10
    Total tests: 187
    The post was NOT equal to the resulting state: 3
    Succeeded: 184
    Success rate of: 98.395722

  stCreateTest                          3m10
    Total tests: 202
    The post was NOT equal to the resulting state: 4
    Succeeded: 198
    Success rate of: 98.019802

  stDelegatecallTestHomestead           0m48
    Total tests: 33
    The post was NOT equal to the resulting state: 6
    Succeeded: 27
    Success rate of: 81.818182

  stEIP150singleCodeGasPrices           7m15
    Total tests: 450
    The post was NOT equal to the resulting state: 0
    Succeeded: 450
    Success rate of: 100.000000

  stEIP150Specific                      0m38
    Total tests: 25
    The post was NOT equal to the resulting state: 0
    Succeeded: 25
    Success rate of: 100.000000

  stEIP1559                             20m38
    Total tests: 1845
    The post was NOT equal to the resulting state: 2
    Succeeded: 1843
    Success rate of: 99.891599

  stEIP158Specific                      0m25
    Total tests: 8
    The post was NOT equal to the resulting state: 0
    Succeeded: 8
    Success rate of: 100.000000

  stEIP2930                             2m27
    Total tests: 140
    The post was NOT equal to the resulting state: 7
    Succeeded: 133
    Success rate of: 95.000000

  stEIP3607                             0m27
    Total tests: 12
    The post was NOT equal to the resulting state: 0
    Succeeded: 12
    Success rate of: 100.000000

  stExample                             0m54
    Total tests: 39
    The post was NOT equal to the resulting state: 0
    Succeeded: 39
    Success rate of: 100.000000

  stExtCodeHash                         1m27
    Total tests: 69
    The post was NOT equal to the resulting state: 0
    Succeeded: 69
    Success rate of: 100.000000

  stHomesteadSpecific                   0m19
    Total tests: 5
    The post was NOT equal to the resulting state: 0
    Succeeded: 5
    Success rate of: 100.000000

  stInitCodeTest                        0m37
    Total tests: 22
    The post was NOT equal to the resulting state: 0
    Succeeded: 22
    Success rate of: 100.000000

  stLogTests                            1m2
    Total tests: 46
    The post was NOT equal to the resulting state: 0
    Succeeded: 46
    Success rate of: 100.000000

  stMemExpandingEIP150Calls             0m26
    Total tests: 14
    The post was NOT equal to the resulting state: 0
    Succeeded: 14
    Success rate of: 100.000000

  stMemoryStressTest                    2m46
    Total tests: 82
    The post was NOT equal to the resulting state: 0
    Succeeded: 82
    Success rate of: 100.000000

  stMemoryTest                          10m29
    Total tests: 578
    The post was NOT equal to the resulting state: 11
    Succeeded: 567
    Success rate of: 98.096886

  stNonZeroCallsTest                    0m38
    Total tests: 24
    The post was NOT equal to the resulting state: 0
    Succeeded: 24
    Success rate of: 100.000000

  stPreCompiledContracts                15m21
    Total tests: 960
    The post was NOT equal to the resulting state: 7
    Succeeded: 953
    Success rate of: 99.270833

  stPreCompiledContracts2               56m40

  stQuadraticComplexityTest             6m32
    Total tests: 32
    The post was NOT equal to the resulting state: 13
    Succeeded: 19
    Success rate of: 59.375000

  stRandom                              6m5
    Total tests: 310
    The post was NOT equal to the resulting state: 9
    Succeeded: 301
    Success rate of: 97.096774

  stRandom2                             3m50
    Total tests: 221
    The post was NOT equal to the resulting state: 7
    Succeeded: 214
    Success rate of: 96.832579

  stRecursiveCreate                     0m15
    Total tests: 1
    The post was NOT equal to the resulting state: 0
    Succeeded: 1
    Success rate of: 100.000000

  stRefundTest                          0m43
    Total tests: 26
    The post was NOT equal to the resulting state: 0
    Succeeded: 26
    Success rate of: 100.000000

  stReturnDataTest                      4m56
    Total tests: 273
    The post was NOT equal to the resulting state: 19
    Succeeded: 254
    Success rate of: 93.040293

  stRevertTest                          4m44
    Total tests: 271
    The post was NOT equal to the resulting state: 4
    Succeeded: 267
    Success rate of: 98.523985

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
    The post was NOT equal to the resulting state: 0
    Succeeded: 23
    Success rate of: 100.000000

  stSpecialTest                         0m35
    Total tests: 22
    The post was NOT equal to the resulting state: 1
    Succeeded: 21
    Success rate of: 95.454545

  stSStoreTest                          9m10
    Total tests: 475
    The post was NOT equal to the resulting state: 0
    Succeeded: 475
    Success rate of: 100.000000

  stStackTests                          3m53
    Total tests: 209
    The post was NOT equal to the resulting state: 1
    Succeeded: 208
    Success rate of: 99.521531

  stStaticCall                          12m33
    Total tests: 478
    The post was NOT equal to the resulting state: 60
    Succeeded: 418
    Success rate of: 87.447699

  stStaticFlagEnabled                   1m28
    Total tests: 34
    The post was NOT equal to the resulting state: 0
    Succeeded: 34
    Success rate of: 100.000000

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
    The post was NOT equal to the resulting state: 1
    Succeeded: 258
    Success rate of: 99.613900

  stTransitionTest                      0m20
    Total tests: 6
    The post was NOT equal to the resulting state: 0
    Succeeded: 6
    Success rate of: 100.000000

  stWalletTest                          0m58
    Total tests: 46
    The post was NOT equal to the resulting state: 0
    Succeeded: 46
    Success rate of: 100.000000

  stZeroCallsRevert                     0m29
    Total tests: 16
    The post was NOT equal to the resulting state: 0
    Succeeded: 16
    Success rate of: 100.000000

  stZeroCallsTest                       0m38
    Total tests: 24
    The post was NOT equal to the resulting state: 0
    Succeeded: 24
    Success rate of: 100.000000

  stZeroKnowledge                       24m49
    Total tests: 944
    The post was NOT equal to the resulting state: 0
    Succeeded: 944
    Success rate of: 100.000000

  stZeroKnowledge2                      9m40
    Total tests: 519
    The post was NOT equal to the resulting state: 0
    Succeeded: 519
    Success rate of: 100.000000

  VMTests                               9m16
    Total tests: 572
    The post was NOT equal to the resulting state: 14
    Succeeded: 558
    Success rate of: 97.552448
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
  Total tests: 0
  The post was NOT equal to the resulting state: 0
  Succeeded: 0
  Success rate of: NaN
^^^ No Cancun tests here
-/
/-
ValidBlocks                             15m40
  Total tests: 439
  The post was NOT equal to the resulting state: 12
  Succeeded: 427
  Success rate of: 97.266515
-/
def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def main : IO Unit := do
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
        ("EthereumTests/BlockchainTests")

  let mut discardedFiles := #[]
  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]

  let mut numFailedTest := 0
  let mut numSuccess := 0

  if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile
  for testFile in testFiles do
    if fileBlacklist.contains testFile then continue
    dbg_trace s!"File under test: {testFile}"
    let res ←
      ExceptT.run <|
        EvmYul.Conform.processTestsOfFile
          -- (whitelist := #["sstore_0to0_d8g1v0_Cancun"])

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
