@[extern "testme"]
opaque testme : UInt32 → UInt32

namespace sha256

abbrev LengthSha256 : Nat := 32

def Sha256Digest : Type := { arr : ByteArray // arr.size = LengthSha256 }

instance : Inhabited Sha256Digest := ⟨⟨.mkArray LengthSha256 0⟩, rfl⟩

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

end sha256

namespace blake2b64

-- @[extern "blake2b64"]
-- opaque blake2b64 (input : @& ByteArray) (len : USize) : ByteArray

-- def BLAKE2b64 (d : ByteArray) : Except String ByteArray :=
--   pure <| blake2b64 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213    then throw "error"
  if d[212]! ∉ [0, 1] then throw "error"
  return BLAKE2Compress d

end blake2b64
