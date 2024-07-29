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

sender = secp256k1_recover(r, s, v, msg_hash)

print(bytes.hex(sender), end = '')

