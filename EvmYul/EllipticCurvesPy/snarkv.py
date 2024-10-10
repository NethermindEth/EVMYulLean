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

data = bytes.fromhex(sys.argv[1])

# OPERATION
if len(data) % 192 != 0:
    print('error', end = '')
    sys.exit()
result = BNF12.from_int(1)
for i in range(len(data) // 192):
    values = []
    for j in range(6):
        value = U256.from_be_bytes(
            data[i * 192 + 32 * j : i * 192 + 32 * (j + 1)]
        )
        if value >= ALT_BN128_PRIME:
            print('error', end = '')
            sys.exit()
        values.append(int(value))

    try:
        p = BNP(BNF(values[0]), BNF(values[1]))
        q = BNP2(
            BNF2((values[3], values[2])), BNF2((values[5], values[4]))
        )
    except ValueError:
        print('error', end = '')
        sys.exit()

    if p.mul_by(ALT_BN128_CURVE_ORDER) != BNP.point_at_infinity():
        print('error', end = '')
        sys.exit()
    if q.mul_by(ALT_BN128_CURVE_ORDER) != BNP2.point_at_infinity():
        print('error', end = '')
        sys.exit()
    if p != BNP.point_at_infinity() and q != BNP2.point_at_infinity():
        result = result * pairing(q, p)

if result == BNF12.from_int(1):
    output = U256(1).to_be_bytes32()
else:
    output = U256(0).to_be_bytes32()

print(bytes.hex(output))
