use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned};
use revm_precompile::blake2::algo::compress;

#[unsafe(no_mangle)]
pub extern "C" fn blake2compressb64(input: LeanByteArray<LeanBorrowed<'_>>) -> LeanByteArray<LeanOwned> {
    let data = input.as_bytes();
    // Parse 213-byte input: rounds[4] + h[64] + m[128] + t[16] + f[1]
    let rounds = u32::from_be_bytes(data[0..4].try_into().unwrap());
    let mut h = [0u64; 8];
    for (i, chunk) in data[4..68].chunks_exact(8).enumerate() {
        h[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    let mut m = [0u64; 16];
    for (i, chunk) in data[68..196].chunks_exact(8).enumerate() {
        m[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    let t = [
        u64::from_le_bytes(data[196..204].try_into().unwrap()),
        u64::from_le_bytes(data[204..212].try_into().unwrap()),
    ];
    let f = data[212] != 0;

    compress(rounds as usize, &mut h, m, t, f);

    let mut output = [0u8; 64];
    for (i, &val) in h.iter().enumerate() {
        output[i * 8..(i + 1) * 8].copy_from_slice(&val.to_le_bytes());
    }
    LeanByteArray::from_bytes(&output)
}
