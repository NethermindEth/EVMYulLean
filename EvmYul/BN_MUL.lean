import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBN_MUL (x₀ y₀ n : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ n
  where pythonCommandOfInput (x₀ y₀ n : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/bn_mul.py", x₀, y₀, n]
  }

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobBN_MUL (toHex x₀) (toHex y₀) (toHex n)
