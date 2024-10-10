import sys
from base_types import U256, Uint
from alt_bn128 import (
    ALT_BN128_CURVE_ORDER,
    ALT_BN128_PRIME,
    BNF,
    BNF2,
    BNF12,
    BNP,
    BNP2,
    pairing,
)
from blake2 import Blake2b

data = bytes.fromhex(sys.argv[1])
if len(data) != 213:
    print('error', end = '')
    sys.exit()

blake2b = Blake2b()
rounds, h, m, t_0, t_1, f = blake2b.get_blake2_parameters(data)

if f not in [0, 1]:
    print('error', end = '')
    sys.exit()

output = blake2b.compress(rounds, h, m, t_0, t_1, f)
print(bytes.hex(output))
