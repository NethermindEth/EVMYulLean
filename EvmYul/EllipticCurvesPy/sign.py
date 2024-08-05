from typing import Tuple
from hash import Hash32
from base_types import Bytes, Bytes32, U256, Uint
import sys
import coincurve

def secp256k1_sign(msg_hash: Hash32, secret_key: int) -> Tuple[U256, ...]:
    """
    Returns the signature of a message hash given the secret key.
    """
    private_key = coincurve.PrivateKey.from_int(secret_key)
    signature = private_key.sign_recoverable(msg_hash, hasher=None)

    return (
        U256.from_be_bytes(signature[0:32]),
        U256.from_be_bytes(signature[32:64]),
        U256(signature[64]),
    )

msg_hash : Hash32 = bytes.fromhex(sys.argv[1])

pr : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[2]), "big")

res = secp256k1_sign(msg_hash, pr)

print(hex(res[0])[2:]) # r
print(hex(res[1])[2:]) # s
print(hex(res[2])[2:], end = '') # v
