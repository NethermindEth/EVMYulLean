-- Requires the following python packages: coincurve, typing-extensions

import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels
import EvmYul.SpongeHash.Keccak256

def secp256k1n : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337

def blobECDSARECOVER (e v r s : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput e v r s
  where pythonCommandOfInput (e v r s : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/recover.py", e, v, r, s]
  }

def blobSign (e pᵣ : String) : List String :=
  (String.split · Char.isWhitespace) ∘ totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput e pᵣ
  where pythonCommandOfInput (e pᵣ : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/sign.py", e, pᵣ]
  }

-- Appendix F. Signing Transactions

def ECDSASIGN (e pᵣ : ByteArray) : Except String (ByteArray × ByteArray × ByteArray) := do
  let [r, s, v] := blobSign (toHex e) (toHex pᵣ) | .error "error"
  let v ← ByteArray.ofBlob <| padLeft 2 v -- 2 characters means 1 byte
  let r ← ByteArray.ofBlob <| padLeft 64 r -- 64 characters means 23
  let s ← ByteArray.ofBlob <| padLeft 64 s -- 64 characters means 23
  .ok (v, r, s)

def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  match blobECDSARECOVER (toHex e) (toHex v) (toHex r) (toHex s) with
    | "error" => .error "ECDSARECOVER failed"
    | s => ByteArray.ofBlob <| padLeft 128 s /- 128 characters means 64 bytes -/

open Batteries
