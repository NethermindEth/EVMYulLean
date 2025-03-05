import sys
import hashlib
import ctypes
ctypes.CDLL("libssl.so").OSSL_PROVIDER_load(None, b"legacy")

from base_types import Bytes

def left_pad_zero_bytes(value: Bytes, size: int) -> Bytes:
    """
    Left pad zeroes to `value` if it's length is less than the given `size`.

    Parameters
    ----------
    value :
        The byte string that needs to be padded.
    size :
        The number of bytes that need that need to be padded.

    Returns
    -------
    left_padded_value: `ethereum.base_types.Bytes`
        left padded byte string of given `size`.
    """
    return value.rjust(size, b"\x00")

data = bytes.fromhex(sys.argv[1])
print("data")
hash_bytes = hashlib.new("ripemd160", data).digest()
print("hash_bytes")
padded_hash = left_pad_zero_bytes(hash_bytes, 32)
print("padded_hash")
output = padded_hash
print("output")
print(bytes.hex(output), end = '')
