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

  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "VMTests")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stZeroKnowledge2")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stZeroKnowledge")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stZeroCallsTest")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stZeroCallsRevert")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stWalletTest")
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stTransitionTest") -- TODO: Parser error.
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stTimeConsuming") -- TODO: Parser error.
  -- let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests" / "stSystemOperationsTest") -- TODO: Takes too long

  -- let appendDir := "stZeroKnowledge2" 
  let testFiles ← Array.filter isTestFile <$> System.FilePath.walkDir ("EthereumTests" / "BlockchainTests" / "GeneralStateTests") -- TODO: Takes too long

  
  -- let testFiles := #[SimpleFile]
  -- let testFiles := #[BuggyFile]
  -- let testFiles := #[SpecificFile]
  -- let testFiles := #[BuggyFile]

  let mut dbgCount := 2^20

  for testFile in testFiles do
    -- dbg_trace s!"testFile: {testFile}"
    if dbgCount == 0 then break

    -- IO.println s!"File under test: {testFile}"
    let res ← ExceptT.run <| EvmYul.Conform.processTestsOfFile testFile -- (whitelist := #["sha3_d5g0v0_Cancun"])
    match res with
      | .error err         => IO.println s!"Error: {repr err}"
      | .ok    testresults => -- IO.println s!"{repr testresults}"
                              -- IO.println "Tests managed to not crash Lean."
                              -- IO.println s!""
                              pure ()

    dbgCount := dbgCount - 1

-- #eval main ["EthereumTests"]
