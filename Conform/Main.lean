import Conform.TestRunner

-- def TestsSubdir := "BlockchainTests"
-- def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def SimpleFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/sdiv.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/exp.json"
def BuggyFile := "Conform/testfile.json"
-- def BuggyFile := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmTests/calldatacopy.json"
def SpecificFile := "EthereumTests/BlockchainTests/ValidBlocks/bcRandomBlockhashTest/randomStatetest573BC.json"

def TestsSubdir := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

def main (args : List String) : IO Unit := do
  if args.length != 1 then IO.println "Usage: conform <path to 'EthereumTests'>"; return ()

  let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests")

  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]

  for testFile in testFiles do
    IO.println s!"File under test: {testFile}"
    let res ← ExceptT.run <| EvmYul.Conform.processTestsOfFile testFile -- (whitelist := #["sha3_d5g0v0_Cancun"])
    match res with
      | .error err         => IO.println s!"Error: {repr err}"
      | .ok    testresults => -- IO.println s!"{repr testresults}"
                              -- IO.println "Tests managed to not crash Lean."
                              -- IO.println s!""
                              pure ()
-- #eval main ["EthereumTests"]
