from hash import keccak256
from base_types import Bytes
import sys

fileName : Bytes = sys.argv[1]
f = open(fileName, "r")
data = bytes.fromhex(f.read())
r = keccak256(data)
print(bytes.hex(r), end = '')    
f.close()
