#include <stdint.h>
#include "lean/lean.h"
#include "sha-256.h"
#include <stdio.h>

extern uint32_t testme(uint32_t x) { return x + 10; }

extern lean_obj_res sha256(b_lean_obj_arg input, size_t len)
{
  uint8_t hash[32];
  calc_sha_256(hash, lean_sarray_cptr(input), len);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(32));
  for (int i = 0; i < 32; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}

// extern void sha256(uint8_t hash[SIZE_OF_SHA_256_HASH], const void *input, size_t len)
// {
// 	struct Sha_256 sha_256;
// 	sha_256_init(&sha_256, hash);
// 	sha_256_write(&sha_256, input, len);
// 	(void)sha_256_close(&sha_256);
// }