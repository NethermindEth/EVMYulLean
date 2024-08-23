import EvmYul.Wheels
import Conform.Wheels

unsafe def unsafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ :=
  match unsafeIO io with
    | Except.ok    a => a
    | Except.error _ => panic! "unsafePerformIO was a not great idea after all"

@[implemented_by unsafePerformIO]
def totallySafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ := Inhabited.default

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

/-- Add `0`s to make the hex representation valid for `ByteArray.ofBlob` -/
def padLeft (n : ℕ) (s : String) :=
  let l := s.length
  if l < n then String.replicate (n - l) '0' ++ s else s

-- Appendix F. Signing Transactions

def ECDSASIGN (e pᵣ : ByteArray) : Except String (ByteArray × ByteArray × ByteArray) := do
  let [r, s, v] := blobSign (toHex e) (toHex pᵣ) | .error "error"
  let v ← ByteArray.ofBlob <| padLeft 2 v -- 2 characters means 1 byte
  let r ← ByteArray.ofBlob <| padLeft 64 r -- 64 characters means 23
  let s ← ByteArray.ofBlob <| padLeft 64 s -- 64 characters means 23
  .ok (v, r, s)

def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| padLeft 128 /- 128 characters means 64 bytes -/ <|
    blobECDSARECOVER (toHex e) (toHex v) (toHex r) (toHex s)

/-- Example of private key -/
private def pᵣ : ByteArray :=
  ⟨#[32, 128, 101, 162, 71, 237, 190, 93, 244, 216, 111, 189, 192, 23, 19, 3, 242, 58, 118, 150, 27, 233, 246, 1, 56, 80, 221, 43, 220, 117, 155, 187]⟩
/-- Example of public key -/
private def pᵤ : ByteArray :=
  ⟨#[131, 107, 53, 160, 38, 116, 62, 130, 58, 144, 160, 238, 59, 145, 191, 97, 92, 106, 117, 126, 43, 96, 185, 225, 220, 24, 38, 253, 13, 209, 97, 6, 247, 188, 30, 129, 121, 246, 101, 1, 95, 67, 198, 200, 31, 57, 6, 47, 194, 8, 110, 216, 73, 98, 92, 6, 224, 70, 151, 105, 139, 33, 133, 94]⟩

/-- Example of message hash -/
private def e₀ : ByteArray :=
  ⟨⟨List.replicate 32 0⟩⟩
/-- Example of message hash -/
private def e : ByteArray :=
  ⟨#[154, 89, 239, 188, 71, 27, 83, 73, 28, 128, 56, 253, 93, 95, 227, 190, 10, 34, 152, 115, 48, 43, 175, 186, 144, 193, 159, 190, 125, 124, 127, 53]⟩

-- Signed transaction for the specific `e₀` an `pᵣ` above
private def v₀ : ByteArray :=
  ⟨#[1]⟩
private def r₀ : ByteArray :=
  ⟨#[181, 202, 66, 174, 114, 67, 27, 102, 5, 30, 236, 183, 16, 106, 249, 86, 8, 22, 3, 8, 150, 251, 247, 198, 14, 241, 208, 68, 161, 57, 64, 140]⟩
private def s₀ : ByteArray :=
  ⟨#[29, 153, 188, 72, 120, 25, 201, 144, 156, 94, 234, 95, 10, 161, 198, 161, 130, 110, 229, 37, 229, 81, 213, 16, 3, 36, 220, 52, 248, 2, 226, 69]⟩

-- Signed transaction for the specific `e` an `pᵣ` above
private def v : ByteArray :=
  ⟨#[0]⟩
private def r : ByteArray :=
  ⟨#[212, 11, 145, 56, 30, 30, 236, 163, 79, 72, 88, 167, 159, 244, 243, 22, 80, 102, 249, 58, 118, 186, 15, 6, 120, 72, 169, 98, 49, 47, 24, 239]⟩
private def s : ByteArray :=
  ⟨#[14, 134, 252, 228, 141, 225, 12, 107, 78, 7, 176, 161, 117, 135, 123, 200, 36, 187, 246, 210, 8, 154, 80, 243, 177, 30, 36, 173, 13, 92, 129, 115]⟩

-- -- Using `pᵣ` to sign the message `e₀`
-- private example :
--   (ECDSASIGN e₀ pᵣ).toOption = (Except.ok (v₀, r₀, s₀) : Except String _).toOption
-- := by native_decide

-- -- Getting the same `pᵤ` back
-- private example :
--   (ECDSARECOVER e₀ v₀ r₀ s₀).toOption = (Except.ok pᵤ : Except String _).toOption
-- := by native_decide

-- -- Using `pᵣ` to sign the message `e`
-- private example :
--   (ECDSASIGN e pᵣ).toOption = (Except.ok (v, r, s) : Except String _).toOption
-- := by native_decide

-- -- Getting the same `pᵤ` back
-- private example :
--   (ECDSARECOVER e v r s).toOption = (Except.ok pᵤ : Except String _).toOption
-- := by native_decide
