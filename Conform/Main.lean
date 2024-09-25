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
  Cancun                                6m0
    Total tests: 189
    The post was NOT equal to the resulting state: 82
    Succeeded: 107
    Success rate of: 56.613757

  Pyspecs                               16m57
    Total tests: 2150
    The post was NOT equal to the resulting state: 1804
    Succeeded: 346
    Success rate of: 16.093023

  Shanghai                              0m42
    Total tests: 27
    The post was NOT equal to the resulting state: 23
    Succeeded: 4
    Success rate of: 14.814815

  stArgsZeroOneBalance                  1m59
    Total tests: 96
    The post was NOT equal to the resulting state: 18
    Succeeded: 78
    Success rate of: 81.250000

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

  stCallCreateCallCodeTest              1m16
    Total tests: 55
    The post was NOT equal to the resulting state: 28
    Succeeded: 27
    Success rate of: 49.090909

  stCallDelegateCodesCallCodeHomestead  1m9

  stCallDelegateCodesHomestead          -

  stChainId                             0m16

  stCodeCopyTest                        0m20

  stCodeSizeLimit                       0m27

  stCreate2                             3m28
    Total tests: 183
    The post was NOT equal to the resulting state: 114
    Succeeded: 69
    Success rate of: 37.704918

  stCreateTest                          3m31
    Total tests: 198
    The post was NOT equal to the resulting state: 147
    Succeeded: 51
    Success rate of: 25.757576

  stDelegatecallTestHomestead           1m

  stEIP150singleCodeGasPrices           8m37
    Total tests: 450
    The post was NOT equal to the resulting state: 450
    Succeeded: 0
    Success rate of: 0.000000

  stEIP150Specific                      0m38

  stEIP1559                             16m53
    Total tests: 1845
    The post was NOT equal to the resulting state: 949
    Succeeded: 896
    Success rate of: 48.563686

  stEIP158Specific                      0m22

  stEIP2930                             1m37

  stEIP3607                             0m27

  stExample                             1m

  stExtCodeHash                         1m32

  stHomesteadSpecific                   0m23

  stInitCodeTest                        0m42

  stLogTests                            1m6

  stMemExpandingEIP150Calls             0m33

  stMemoryStressTest                    2m46
    Total tests: 82
    The post was NOT equal to the resulting state: 3
    Succeeded: 79
    Success rate of: 96.341463

  stMemoryTest                          4m12
    Total tests: 218
    The post was NOT equal to the resulting state: 97
    Succeeded: 121
    Success rate of: 55.504587

  stNonZeroCallsTest                    0m34

  stPreCompiledContracts                -

  stPreCompiledContracts2               -

  stQuadraticComplexityTest             0m41

  stRandom                              6m5
    Total tests: 308
    The post was NOT equal to the resulting state: 54
    Succeeded: 254
    Success rate of: 82.467532

  stRandom2                             3m24

  stRecursiveCreate                     0m15

  stRefundTest                          0m34

  stReturnDataTest                      4m35
    Total tests: 273
    The post was NOT equal to the resulting state: 229
    Succeeded: 44
    Success rate of: 16.117216

  stRevertTest                          4m54
    Total tests: 262
    The post was NOT equal to the resulting state: 61
    Succeeded: 201
    Success rate of: 76.717557

  stSelfBalance                         0m50

  stShift                               0m50

  stSLoadTest                           0m14

  stSolidityTest                        0m33

  stSpecialTest                         0m30

  stSStoreTest                          9m10
    Total tests: 475
    The post was NOT equal to the resulting state: 116
    Succeeded: 359
    Success rate of: 75.578947

  stStackTests                          3m32

  stStaticCall                          7m56
    Total tests: 469
    The post was NOT equal to the resulting state: 397
    Succeeded: 72
    Success rate of: 15.351812

  stStaticFlagEnabled                   0m43

  stSystemOperationsTest                1m26

  stTimeConsuming                       81m20
    Total tests: 5190
    The post was NOT equal to the resulting state: 2
    Succeeded: 5188
    Success rate of: 99.961464

  stTransactionTest                     3m28

  stTransitionTest                      0m19

  stWalletTest                          0m52

  stZeroCallsRevert                     0m28

  stZeroCallsTest                       0m35

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

  VMTests                               10m26
    Total tests: 571
    The post was NOT equal to the resulting state: 106
    Succeeded: 465
    Success rate of: 81.436077
-/

def directoryBlacklist : List System.FilePath :=
  [
    "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2"
  , "EthereumTests/BlockchainTests/GeneralStateTests/stCallDelegateCodesHomestead"
  ]

def fileBlacklist : List System.FilePath :=
  [ "EthereumTests/BlockchainTests/GeneralStateTests/stMemoryTest/buffer.json"
  ]

def main : IO Unit := do
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
        ("EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs")

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
