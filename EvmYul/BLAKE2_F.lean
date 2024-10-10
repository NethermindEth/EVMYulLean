import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/blake2_f.py", data]
  }

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s
