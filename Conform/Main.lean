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
                         (result : Lean.RBMap String EvmYul.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

def main (args : List String) : IO Unit := do
  if args.length != 1 then IO.println "Usage: conform <path to 'EthereumTests'>"; return ()

  let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests")

  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]

  let mut numThrewAlongTheWay := 0
  let mut numFailedTest := 0
  let mut numSuccess := 0

  for testFile in testFiles do
    dbg_trace s!"File under test: {testFile}"
    let res ← ExceptT.run <| EvmYul.Conform.processTestsOfFile testFile
    match res with
      | .error err         => IO.println s!"Error: {repr err}"; numThrewAlongTheWay := numThrewAlongTheWay + 1
      | .ok    testresults => if ← basicSuccess testFile testresults
                              then numSuccess := numSuccess + 1
                              else numFailedTest := numFailedTest + 1

  let total := numThrewAlongTheWay + numFailedTest + numSuccess
  IO.println s!"Total tests: {total}"
  IO.println s!"Threw along the way: {numThrewAlongTheWay}"
  IO.println s!"The post was NOT equal to the resulting state: {numFailedTest}"
  IO.println s!"Succeeded: {numSuccess}"
  IO.println s!"Success rate of: {(numSuccess.toFloat / total.toFloat) * 100.0}"

-- #eval main ["EthereumTests"]
