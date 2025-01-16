import sys
from trie import Trie, root, trie_set
from base_types import Bytes
from typing import (
    Optional,
)
n = int(sys.argv[1])

trie: Trie[Bytes, Optional[Bytes]] = Trie(
        secured=False, default=None
    )

for i in range(n):
    trie_set(trie, bytes.fromhex(sys.argv[2*i+2]), bytes.fromhex(sys.argv[2*i+3]))
r = root(trie)

print(bytes.hex(r), end = '')
