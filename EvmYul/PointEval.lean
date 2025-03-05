import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobPointEval (data : String) : String :=
  -- dbg_trace s!"EvmYul/EllipticCurvesPy/point_evaluation.py"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/point_evaluation.py", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s
