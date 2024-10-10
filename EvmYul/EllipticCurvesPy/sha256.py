import sys
import hashlib

data = bytes.fromhex(sys.argv[1])
output = hashlib.sha256(data).digest()
print(bytes.hex(output), end = '')
