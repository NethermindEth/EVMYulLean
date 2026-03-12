#include <stdint.h>
#include "lean/lean.h"
#include "sha-256.h"
#include <stdio.h>
#include <stdbool.h> 
#include "sha3.h"

#define SHA256_OUTPUT_SIZE 32
#define KECCAK256_OUTPUT_SIZE 32

extern lean_obj_res sha256(b_lean_obj_arg input, size_t len) {
  uint8_t hash[SHA256_OUTPUT_SIZE];
  calc_sha_256(hash, lean_sarray_cptr(input), len);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(SHA256_OUTPUT_SIZE));
  for (int i = 0; i < SHA256_OUTPUT_SIZE; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}

extern lean_obj_arg memset_zero(size_t n) {
  lean_object* res = lean_alloc_sarray(1, n, n);
  uint8_t* it = lean_sarray_cptr(res);
  memset(it, 0, n);
  return res;
}

extern lean_obj_arg keccak256(b_lean_obj_arg input, size_t inBytes) {
  uint8_t hash[KECCAK256_OUTPUT_SIZE];
  sha3_HashBuffer(256, SHA3_FLAGS_KECCAK, lean_sarray_cptr(input), inBytes, hash, KECCAK256_OUTPUT_SIZE);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(KECCAK256_OUTPUT_SIZE));
  for (int i = 0; i < KECCAK256_OUTPUT_SIZE; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}
