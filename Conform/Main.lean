import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/correct_increasing_blob_gas_costs.json"

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
  Cancun                                3m24
  Pyspecs                               18m5
  Shanghai                              0m45
  stArgsZeroOneBalance                  1m57
  stAttackTest                          0m16
  stBadOpcode                           76m31
  stBugs                                0m23
  stCallCodes                           -
  stCallCreateCallCodeTest              -
  stCallDelegateCodesCallCodeHomestead  1m9
  stCallDelegateCodesHomestead          1m5
  stChainId                             0m16
  stCodeCopyTest                        0m20
  stCodeSizeLimit                       0m27
  stCreate2                             3m35
  stCreateTest                          3m51
  stDelegatecallTestHomestead           1m
  stEIP150singleCodeGasPrices           8m28
  stEIP150Specific                      0m38
  stEIP1559                             17m45
  stEIP158Specific                      0m22
  stEIP2930                             1m37
  stEIP3607                             0m27
  stExample                             1m
  stExtCodeHash                         1m32
  stHomesteadSpecific                   0m23
  stInitCodeTest                        0m42
  stLogTests                            1m6
  stMemExpandingEIP150Calls             0m33
  stMemoryStressTest                    3m39
  stMemoryTest                          10m35
  stNonZeroCallsTest                    0m34
  stPreCompiledContracts                -
  stPreCompiledContracts2               -
  stQuadraticComplexityTest             0m41
  stRandom                              4m41
  stRandom2                             3m24
  stRecursiveCreate                     0m15
  stRefundTest                          0m34
  stReturnDataTest                      4m7
  stRevertTest                          4m1
  stSelfBalance                         0m50
  stShift                               0m50
  stSLoadTest                           0m14
  stSolidityTest                        0m33
  stSpecialTest                         0m30
  stSStoreTest                          7m10
  stStackTests                          3m32
  stStaticCall                          6m56
  stStaticFlagEnabled                   0m43
  stSystemOperationsTest                1m26
  stTimeConsuming                       76m55
  stTransactionTest                     3m28
  stTransitionTest                      0m19
  stWalletTest                          0m52
  stZeroCallsRevert                     0m28
  stZeroCallsTest                       0m35
  stZeroKnowledge                       14m40
  stZeroKnowledge2                      8m9
  VMTests                               10m16
-/
def main : IO Unit := do
  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir
        (enter := λ path ↦ -- exclude the following files:
          pure
            (   path != "EthereumTests/BlockchainTests/GeneralStateTests/stCallCodes"
             && path != "EthereumTests/BlockchainTests/GeneralStateTests/stCallCreateCallCodeTest"
             && path != "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts"
             && path != "EthereumTests/BlockchainTests/GeneralStateTests/stPreCompiledContracts2"
             && path != "EthereumTests/BlockchainTests/GeneralStateTests/stEIP150singleCodeGasPrices"
            )
        )
        ("EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest")

  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]

  let mut discardedFiles := #[]

  let mut numFailedTest := 0
  let mut numSuccess := 0

  if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile

  for testFile in testFiles do
    dbg_trace s!"File under test: {testFile}"
    let res ←
      ExceptT.run <|
        EvmYul.Conform.processTestsOfFile
          (whitelist := #["add_d0g0v0_Cancun"])
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
