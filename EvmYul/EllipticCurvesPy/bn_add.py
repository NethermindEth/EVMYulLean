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
x1_bytes = bytes.fromhex(sys.argv[3])
x1_value = U256.from_be_bytes(x1_bytes)
y1_bytes = bytes.fromhex(sys.argv[4])
y1_value = U256.from_be_bytes(y1_bytes)

for i in (x0_value, y0_value, x1_value, y1_value):
    if i >= ALT_BN128_PRIME:
        raise OutOfGasError

try:
    p0 = BNP(BNF(x0_value), BNF(y0_value))
    p1 = BNP(BNF(x1_value), BNF(y1_value))
except ValueError:
    raise OutOfGasError

p = p0 + p1

output = p.x.to_be_bytes32() + p.y.to_be_bytes32()
print(bytes.hex(output), end = '')