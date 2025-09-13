#![feature(generic_const_exprs)]

mod instr;

pub fn array_concat<T, const M: usize, const N: usize>(a_1: [T; M], a_2: [T; N]) -> [T; M + N] {
    let mut a = std::mem::MaybeUninit::<[T; M + N]>::uninit();
    let p = a.as_mut_ptr() as *mut T;
    unsafe {
        std::ptr::copy_nonoverlapping(a_1.as_ptr(), p, M);
        std::ptr::copy_nonoverlapping(a_2.as_ptr(), p.add(M), N);
        a.assume_init()
    }
}

pub fn sign_extend(n: u64, bits: usize) -> u64 {
    let shift = 64 - bits;
    ((n << shift) as i64 >> shift) as u64
}

pub fn extract_bits(n: u64, bits_from: usize, bits_len: usize) -> u64 {
    (n >> bits_from) & ((1 << bits_len) - 1)
}
