import sys
from trie import Trie, root, trie_set
from base_types import Bytes
from typing import (
    Optional,
)

fileName : Bytes = sys.argv[1]
file = open(fileName, "r")
n = int(sys.argv[2])

trie: Trie[Bytes, Optional[Bytes]] = Trie(
        secured=False, default=None
    )

for i in range(n):
    key = file.readline()
    value = file.readline()
    trie_set(trie, bytes.fromhex(key.strip()), bytes.fromhex(value.strip()))
r = root(trie)

print(bytes.hex(r), end = '')
