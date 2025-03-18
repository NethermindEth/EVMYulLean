import EvmYul.PerformIO
import EvmYul.Wheels

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  -- dbg_trace s!"called blobComputeTrieRoot with an array of size {ws.size}"
  -- dbg_trace s!"called blobComputeTrieRoot with data {ws[0]!.2.length}"
  
  totallySafePerformIO do
    /-
      Yes, this makes testing in parallel technically nondeterministic, but it is also the
      fastest to implement.

      This 'using a file trick' to get around big command line arguments should probably go
      at some point.
    -/
    let entropy ← IO.getRandomBytes 3
    let entropy' ← IO.monoNanosNow
    let inputFile := s!"EvmYul/EllipticCurvesPy/trieInput_{entropy}{entropy'}.txt"
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
