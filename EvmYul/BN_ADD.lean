import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBN_ADD (x₀ y₀ x₁ y₁ : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ x₁ y₁
  where pythonCommandOfInput (x₀ y₀ x₁ y₁ : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/bn_add.py", x₀, y₀, x₁, y₁]
  }

def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁)
