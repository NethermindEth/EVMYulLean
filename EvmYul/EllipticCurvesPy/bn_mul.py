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

# OPERATION
x0_bytes = bytes.fromhex(sys.argv[1])
x0_value = U256.from_be_bytes(x0_bytes)
y0_bytes = bytes.fromhex(sys.argv[2])
y0_value = U256.from_be_bytes(y0_bytes)
n = U256.from_be_bytes(bytes.fromhex(sys.argv[3]))

for i in (x0_value, y0_value):
    if i >= ALT_BN128_PRIME:
        print('error', end = '')
        sys.exit()

try:
    p0 = BNP(BNF(x0_value), BNF(y0_value))
except ValueError:
    print('error', end = '')
    sys.exit()

p = p0.mul_by(n)

output = p.x.to_be_bytes32() + p.y.to_be_bytes32()
print(bytes.hex(output), end = '')
