# requires: coincurve, pycryptodome, typing-extensions

# The order of arguments mirrors the yellow paper:
# ECDSARECOVER(e ∈ B_32, v ∈ B_1, r ∈ B_32, s ∈ B_32) ≡ pu ∈ B64
# where e is the hash of the transaction
import sys

from elliptic_curve import secp256k1_recover
from base_types import Bytes, Bytes32, U256, Uint
from hash import Hash32

msg_hash : Hash32 = bytes.fromhex(sys.argv[1])

v : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[2]), "big")
r : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[3]), "big")
s : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[4]), "big")

# r : U256 = Uint(82225988918979265670836577180508950465870808108650505943987126229520646488204)
# s : U256 = Uint(13388699691903258032084613977498615282015119231085051141811208674732178334277)
# v : U256 = Uint(1)

# def secp256k1_recover(r: U256, s: U256, v: U256, msg_hash: Hash32) -> Bytes:
sender = secp256k1_recover(r, s, v, msg_hash)

print(bytes.hex(sender), end = '')

