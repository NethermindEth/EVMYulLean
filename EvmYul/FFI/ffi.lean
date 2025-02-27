@[extern "testme"]
opaque testme : UInt32 → UInt32

namespace sha256

abbrev LengthSha256 : Nat := 32

def Sha256Digest : Type := { arr : ByteArray // arr.size = LengthSha256 }

instance : Inhabited Sha256Digest := ⟨⟨.mkArray LengthSha256 0⟩, rfl⟩

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

end sha256
