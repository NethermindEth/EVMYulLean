#include <stdint.h>
#include "lean/lean.h"
#include "sha-256.h"
#include <stdio.h>

extern uint32_t testme(uint32_t x) { return x + 10; }

extern lean_obj_res sha256(b_lean_obj_arg input, size_t len)
{
	uint8_t* hash = (uint8_t*) malloc(32);
  calc_sha_256(hash, "abc", strlen("abc"));

  lean_obj_res res = lean_mk_empty_array_with_capacity(lean_box(32));
  memcpy(res, hash, 32);

  free(hash);
  return res;
  // calc_sha_256(hash, "abc", strlen("abc"));
}

// extern void sha256(uint8_t hash[SIZE_OF_SHA_256_HASH], const void *input, size_t len)
// {
// 	struct Sha_256 sha_256;
// 	sha_256_init(&sha_256, hash);
// 	sha_256_write(&sha_256, input, len);
// 	(void)sha_256_close(&sha_256);
// }