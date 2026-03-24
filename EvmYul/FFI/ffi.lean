namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw s!"bad size: {d.size} != 213"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw s!"bad flag: {d[212]!}"
  return BLAKE2Compress d

@[extern "ripemd160_hash"]
opaque RIP160 (input : @& ByteArray) : ByteArray

@[extern "memset_zero"]
opaque ByteArray.zeroes (n : USize) : ByteArray

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
