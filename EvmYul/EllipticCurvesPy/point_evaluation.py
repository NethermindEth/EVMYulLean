import sys
"""
Ethereum Virtual Machine (EVM) POINT EVALUATION PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the POINT EVALUATION precompiled contract.
"""
from base_types import Bytes, Bytes32, Bytes48, U256

from kzg import (
    KZGCommitment,
    kzg_commitment_to_versioned_hash,
    verify_kzg_proof,
)

FIELD_ELEMENTS_PER_BLOB = 4096
BLS_MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513  # noqa: E501
VERSIONED_HASH_VERSION_KZG = b"\x01"


data = bytes.fromhex(sys.argv[1])

if len(data) != 192:
    print('error', end = '')
    sys.exit()

versioned_hash = data[:32]
z = Bytes32(data[32:64])
y = Bytes32(data[64:96])
commitment = KZGCommitment(data[96:144])
proof = Bytes48(data[144:192])

# Verify KZG proof with z and y in big endian format
try:
    kzg_proof_verification = verify_kzg_proof(commitment, z, y, proof)
except Exception as e:
    print('error', end = '')
    sys.exit()

if not kzg_proof_verification:
    print('error', end = '')
    sys.exit()

# Return FIELD_ELEMENTS_PER_BLOB and BLS_MODULUS as padded
# 32 byte big endian values
result = Bytes(
    U256(FIELD_ELEMENTS_PER_BLOB).to_be_bytes32()
    + U256(BLS_MODULUS).to_be_bytes32()
)

print(bytes.hex(result), end = '')