import sys
import hashlib

import time

f = open("pythonLogs.txt", "a")
start_time = time.time()

data = bytes.fromhex(sys.argv[1])
output = hashlib.sha256(data).digest()
print(bytes.hex(output), end = '')

t = (time.time() - start_time) * 10 ** 3
if t >= 0.07:
    f.write("SHA256 script finished after " + str(t) + " ms\n")
else:
    f.write("SHA256 script finished fast (< 0.07 ms)\n")
    
f.close()