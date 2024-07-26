import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/sdiv.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/exp.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"

def TestsSubdir := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def main (args : List String) : IO Unit := do
  if args.length != 1 then IO.println "Usage: conform <path to 'EthereumTests'>"; return ()

  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir (args.head! / TestsSubdir)
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "VMTests" / "vmArithmeticTest")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "VMTests" / "vmArithmeticTest")
  
  let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]

  -- let testFiles := #[BuggyFile]

  let mut dbgCount := 42

  for testFile in testFiles do
    if dbgCount == 0 then break

    IO.println s!"File under test: {testFile}"
    let res ← ExceptT.run <| EvmYul.Conform.processTestsOfFile testFile
    match res with
      | .error err         => IO.println s!"Error: {repr err}"
      | .ok    testresults => IO.println s!"{repr testresults}"

    dbgCount := dbgCount - 1

#eval main ["EthereumTests"]
