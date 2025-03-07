import EvmYul.PerformIO
import EvmYul.Wheels

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput ws
  where pythonCommandOfInput (ws : Array (String × String)) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args :=
      #["EvmYul/EllipticCurvesPy/trie_root.py"]
        ++ #[ws.size.repr]
        ++ (ws.map (λ (i, w) ↦ #[i, w])).join
  }
