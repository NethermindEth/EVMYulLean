@[extern "testme"]
opaque testme : UInt32 → UInt32

namespace sha256

abbrev LengthSha256 : Nat := 32

def sha256Digest : Type := { arr : ByteArray // arr.size = LengthSha256 }

end sha256
