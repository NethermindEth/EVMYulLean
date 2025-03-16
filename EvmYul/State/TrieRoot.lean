import EvmYul.PerformIO
import EvmYul.Wheels

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  -- dbg_trace s!"called blobComputeTrieRoot with an array of size {ws.size}"
  -- dbg_trace s!"called blobComputeTrieRoot with data {ws[0]!.2.length}"
  let inputFile := "EvmYul/EllipticCurvesPy/trieInput.txt"
  totallySafePerformIO do
    IO.FS.withFile inputFile .write λ h ↦
      forM ws.data λ s ↦ do
        h.putStrLn s.1
        h.putStrLn s.2
    let result ← IO.Process.run (pythonCommandOfInput inputFile ws)
    IO.FS.removeFile inputFile
    pure result
 where
  pythonCommandOfInput (inputFile : String) (ws : Array (String × String)) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args :=
      #["EvmYul/EllipticCurvesPy/trie_root.py"]
        ++ #[inputFile]
        ++ #[ws.size.repr]
        -- ++ (ws.map (λ (i, w) ↦ #[i, w])).join
  }
