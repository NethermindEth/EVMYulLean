import EvmYul.PerformIO
import EvmYul.Wheels
import Conform.Wheels

def blobRIP160 (d : String) : String :=
  -- dbg_trace s!"EvmYul/EllipticCurvesPy/rip160.py with d: {d} will run: {pythonCommandOfInput d |>.cmd} {pythonCommandOfInput d |>.args}"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/rip160.py", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobRIP160 (toHex d)
