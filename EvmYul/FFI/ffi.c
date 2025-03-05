#include <stdint.h>
#include "lean/lean.h"
#include "sha-256.h"
#include <stdio.h>
#include <stdbool.h> 

#define SHA256_OUTPUT_SIZE 32

// #define BLAKE2B_OUTPUT_SIZE 64
#define BLAKE2B_COMPRESS_SIZE 8
#define BLAKE2B_KEY_LENGTH    8

extern lean_obj_res sha256(b_lean_obj_arg input, size_t len) {
  uint8_t hash[SHA256_OUTPUT_SIZE];
  calc_sha_256(hash, lean_sarray_cptr(input), len);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(SHA256_OUTPUT_SIZE));
  for (int i = 0; i < SHA256_OUTPUT_SIZE; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}

// Implementation based on https://github.com/BLAKE2/BLAKE2/
// with # of rounds parameterised from 12 (BLAKE2) to k < 2^32.

uint64_t rotr64(const uint64_t w, const unsigned int c) {
  return (w >> c) | (w << (64 - c));
}

#define G(a, b, c, d, e, f)         \
  do {                              \
    v[a] = v[a] + v[b] + e;         \
    v[d] = rotr64(v[d] ^ v[a], 32); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 24); \
    v[a] = v[a] + v[b] + f;         \
    v[d] = rotr64(v[d] ^ v[a], 16); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 63); \
  } while(0)

const uint64_t blake2b_IV[8] = {
  0x6A09E667F3BCC908ULL, 0xBB67AE8584CAA73BULL,
  0x3C6EF372FE94F82BULL, 0xA54FF53A5F1D36F1ULL,
  0x510E527FADE682D1ULL, 0x9B05688C2B3E6C1FULL,
  0x1F83D9ABFB41BD6BULL, 0x5BE0CD19137E2179ULL
};

// Do not repeat the last two rows, we'll be MOD 10,
// as we are going 12 -> k rounds.
const uint8_t blake2b_sigma[10][16] = {
  {0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10, 11, 12, 13, 14, 15},
  {14, 10, 4 , 8 , 9 , 15, 13, 6 , 1 , 12, 0 , 2 , 11, 7 , 5 , 3 },
  {11, 8 , 12, 0 , 5 , 2 , 15, 13, 10, 14, 3 , 6 , 7 , 1 , 9 , 4 },
  {7 , 9 , 3 , 1 , 13, 12, 11, 14, 2 , 6 , 5 , 10, 4 , 0 , 15, 8 },
  {9 , 0 , 5 , 7 , 2 , 4 , 10, 15, 14, 1 , 11, 12, 6 , 8 , 3 , 13},
  {2 , 12, 6 , 10, 0 , 11, 8 , 3 , 4 , 13, 7 , 5 , 15, 14, 1 , 9 },
  {12, 5 , 1 , 15, 14, 13, 4 , 10, 0 , 7 , 6 , 3 , 9 , 2 , 8 , 11},
  {13, 11, 7 , 14, 12, 1 , 3 , 9 , 5 , 0 , 15, 4 , 8 , 6 , 2 , 10},
  {6 , 15, 14, 9 , 11, 3 , 0 , 8 , 12, 2 , 13, 7 , 1 , 4 , 10, 5 },
  {10, 2 , 8 , 4 , 7 , 6 , 1 , 5 , 15, 11, 9 , 14, 3 , 12, 13, 0 }
};

static void blake2b_compress_any(
  uint32_t              rounds,
  uint64_t*             h,
  const uint64_t* const m,
  const uint64_t* const t,
  bool                  f
) {
  uint64_t v[16];
  for (int i = 0; i < 8; ++i) {
    v[i] = h[i];
    v[i + 8] = blake2b_IV[i];
  }
  v[12]        ^= t[0];
  v[13]        ^= t[1];
  if (f) v[14] =  ~v[14];

  for (unsigned int i = 0U; i < rounds; ++i) {
    G(0, 4, 8 , 12, m[blake2b_sigma[i % 10][0 ]], m[blake2b_sigma[i % 10][1 ]]);
    G(1, 5, 9 , 13, m[blake2b_sigma[i % 10][2 ]], m[blake2b_sigma[i % 10][3 ]]);
    G(2, 6, 10, 14, m[blake2b_sigma[i % 10][4 ]], m[blake2b_sigma[i % 10][5 ]]);
    G(3, 7, 11, 15, m[blake2b_sigma[i % 10][6 ]], m[blake2b_sigma[i % 10][7 ]]);
    G(0, 5, 10, 15, m[blake2b_sigma[i % 10][8 ]], m[blake2b_sigma[i % 10][9 ]]);
    G(1, 6, 11, 12, m[blake2b_sigma[i % 10][10]], m[blake2b_sigma[i % 10][11]]);
    G(2, 7, 8 , 13, m[blake2b_sigma[i % 10][12]], m[blake2b_sigma[i % 10][13]]);
    G(3, 4, 9 , 14, m[blake2b_sigma[i % 10][14]], m[blake2b_sigma[i % 10][15]]);
  }

  for (int i = 0; i < 8; ++i)
    h[i] ^= v[i] ^ v[i + 8];
}

extern lean_obj_arg blake2compressb64(b_lean_obj_arg input) {
  uint8_t* in = lean_sarray_cptr(input);
  
  // [0; 3] (4 bytes) - big endian, 4 bytes
  uint32_t rounds = (in[3] << 0 * 8) | (in[2] << 1 * 8) |
                    (in[1] << 2 * 8) | ((uint32_t)in[0] << 3 * 8);
  in += 4;

  // [4; 67] (64 bytes) - small endian, 8 bytes, 8 times
  uint64_t h[8];
  for (int i = 0; i < 8; ++i) {
    h[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }
  
  // [68; 195] (128 bytes) - small endian, 8 bytes, 16 times
  uint64_t m[16];
  for (int i = 0; i < 16; ++i) {
    m[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }

  // [196; 211] (16 bytes) - small endian, 8 bytes, 2 times
  uint64_t t[2];
  for (int i = 0; i < 2; ++i) {
    t[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }

  // [212; 212] (1 bytes) - 0 is false, 1 is true
  bool f = *in;

  blake2b_compress_any(rounds, h, m, t, f);

  lean_obj_res res = lean_mk_empty_byte_array(lean_box(BLAKE2B_COMPRESS_SIZE * sizeof(uint64_t)));

  for (int i = 0; i < BLAKE2B_COMPRESS_SIZE * sizeof(uint64_t); ++i)
    lean_byte_array_push(res, *(((uint8_t*)h) + i));

  return res;
}

extern lean_obj_arg memset_zero(size_t n) {
  lean_object* res = lean_alloc_sarray(1, n, n);
  uint8_t* it = lean_sarray_cptr(res);
  memset(it, 0, n);
  return res;
}  
