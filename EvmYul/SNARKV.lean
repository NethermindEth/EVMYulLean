import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobSNARKV (data : String) : String :=
  -- dbg_trace s!"EvmYul/EllipticCurvesPy/snarkv.py"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/snarkv.py", data]
  }

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s
