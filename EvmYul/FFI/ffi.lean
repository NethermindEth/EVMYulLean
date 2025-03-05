namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213    then throw "error"
  if d[212]! ∉ [0, 1] then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
opaque ByteArray.zeroes (n : USize) : ByteArray

end ffi
