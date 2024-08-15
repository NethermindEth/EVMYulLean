import sys
from trie import Trie, root, trie_set
from base_types import Bytes
from typing import (
    Callable,
    Dict,
    Generic,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
    TypeVar,
    Union,
    cast,
)
n = int(sys.argv[1])

withdrawals_trie: Trie[Bytes, Optional[Bytes]] = Trie(
        secured=False, default=None
    )

for i in range(n):
    trie_set(withdrawals_trie, bytes.fromhex(sys.argv[2*i+2]), bytes.fromhex(sys.argv[2*i+3]))
r = root(withdrawals_trie)

print(bytes.hex(r), end = '')
