import sys
import hashlib
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
hash_bytes = hashlib.new("ripemd160", data).digest()
padded_hash = left_pad_zero_bytes(hash_bytes, 20)
output = padded_hash
print(bytes.hex(output), end = '')
