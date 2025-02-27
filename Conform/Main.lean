import Conform.TestRunner
import EvmYul.FFI.ffi

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stStackTests/underflowTest.json"

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

def fileBlacklist : List System.FilePath := []

def main : IO Unit := do
  dbg_trace "The number is: {testme 42}"
  dbg_trace "The hash is: {sha256.sha256 .empty 42}"
  pure ()

-- #eval main

  -- let testFiles ←
  --   Array.filter isTestFile <$>
  --     System.FilePath.walkDir
  --       (enter := λ path ↦ pure <| path ∉ directoryBlacklist)
  --       ("EthereumTests/BlockchainTests")

  -- let mut discardedFiles := #[]
  -- -- let testFiles := #[SimpleFile]
  -- -- let testFiles := #[BuggyFile]
  -- -- let testFiles := #[SpecificFile]

  -- let mut numFailedTest := 0
  -- let mut numSuccess := 0

  -- if ←System.FilePath.pathExists logFile then IO.FS.removeFile logFile
  -- for testFile in testFiles do
  --   if fileBlacklist.contains testFile then continue
  --   dbg_trace s!"File under test: {testFile}"
  --   let res ←
  --     ExceptT.run <|
  --       EvmYul.Conform.processTestsOfFile
  --         -- (whitelist := #["CreateOOGafterMaxCodesize_d4g0v0_Cancun"])
  --         --   #[
  --         --     "21_tstoreCannotBeDosdOOO_d0g0v0_Cancun"
  --         --   , "15_tstoreCannotBeDosd_d0g0v0_Cancun"
  --         --   , "ContractCreationSpam_d0g0v0_Cancun"
  --         --   , "static_Return50000_2_d0g0v0_Cancun"
  --         --   , "static_Call50000_identity_d0g0v0_Cancun"
  --         --   , "static_Call50000_identity_d1g0v0_Cancun"
  --         --   , "static_Call50000_ecrec_d0g0v0_Cancun"
  --         --   , "static_Call50000_ecrec_d0g0v0_Cancun"
  --         --   , "static_Call50000_identity2_d0g0v0_Cancun"
  --         --   , "static_Call50000_identity2_d1g0v0_Cancun"
  --         --   , "static_LoopCallsThenRevert_d0g0v0_Cancun"
  --         --   , "static_LoopCallsThenRevert_d0g1v0_Cancun"
  --         --   , "static_Call50000_d0g0v0_Cancun"
  --         --   , "static_Call50000_d1g0v0_Cancun"
  --         --   , "static_Call50000_rip160_d0g0v0_Cancun"
  --         --   , "static_Call50000_rip160_d1g0v0_Cancun"
  --         --   , "loopMul_d0g0v0_Cancun" -- OOF
  --         --   , "loopMul_d1g0v0_Cancun" -- OOF
  --         --   , "loopMul_d2g0v0_Cancun" -- OOF
  --         --   , "performanceTester_d1g0v0_Cancun"
  --         --   , "performanceTester_d4g0v0_Cancun"
  --         --   , "loopExp_d10g0v0_Cancun" -- OOF
  --         --   , "loopExp_d11g0v0_Cancun" -- OOF
  --         --   , "loopExp_d12g0v0_Cancun" -- OOF
  --         --   , "loopExp_d13g0v0_Cancun"
  --         --   , "loopExp_d14g0v0_Cancun" -- OOF
  --         --   , "loopExp_d8g0v0_Cancun" -- OOF
  --         --   , "loopExp_d9g0v0_Cancun" -- OOF
  --         --   , "Return50000_2_d0g0v0_Cancun"
  --         --   , "Call50000_identity2_d0g1v0_Cancun"
  --         --   , "Call50000_ecrec_d0g1v0_Cancun"
  --         --   , "Return50000_d0g1v0_Cancun"
  --         --   -- , "Call50000_sha256_d0g1v0_Cancun"
  --         --   , "Call50000_d0g1v0_Cancun"
  --         --   , "Callcode50000_d0g1v0_Cancun"
  --         --   , "Call50000_identity_d0g1v0_Cancun"
  --         --   , "QuadraticComplexitySolidity_CallDataCopy_d0g1v0_Cancun"
  --         --   , "static_Call50000_sha256_d0g0v0_Cancun"
  --         --   , "static_Call50000_sha256_d1g0v0_Cancun"
  --         --   ]
  --         -- )

  --         testFile
  --   match res with
  --     | .error err         => discardedFiles := discardedFiles.push (testFile, err)
  --     | .ok    testresults => for (test, result) in testresults do
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
