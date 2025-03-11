import Conform.TestRunner
import EvmYul.FFI.ffi

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
-- def SpecificFile := "EthereumTests/BlockchainTests/GeneralStateTests/stStackTests/underflowTest.json"
def SpecificFile := "EthereumTests/BlockchainTests/InvalidBlocks/bcInvalidHeaderTest/wrongTransactionsTrie.json"

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

def directoryBlacklist : List System.FilePath := []

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

def main : IO Unit := do
  -- dbg_trace "The number is: {testme 42}"
  -- dbg_trace "The hash is: {sha256.sha256 "abc".toUTF8 "abc".length.toUSize}"
  -- dbg_trace s!"The hash is: {blake2b64.blake2b64 "abc".toUTF8 "abc".length.toUSize}"
  -- dbg_trace s!"The hash is: {EvmYul.toHex <| blake2b64.BLAKE2Compress testInput}"
  -- pure ()
  -- pure ()

  -- #eval main
  -- CALLBlake2f_MaxRounds_d0g0v0_Cancun
  -- pure ()
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
  dbg_trace s!"test files: {testFiles}"
  for testFile in testFiles do
    if fileBlacklist.contains testFile then continue
    dbg_trace s!"File under test: {testFile}"
    let res ←
      ExceptT.run <|
        EvmYul.Conform.processTestsOfFile
          -- ( whitelist := #[] )

          testFile
    match res with
      | .error err         => dbg_trace "error!"
                              discardedFiles := discardedFiles.push (testFile, err)
      | .ok    testresults => dbg_trace "ok! - testresults: {repr testresults}"
                              for (test, result) in testresults do
                                dbg_trace s!"test: {test} result: {result}"
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
