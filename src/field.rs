//! Implementation of arithmetic in the field GF(2^255).

use std::cmp;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use std::num;
use std::str::FromStr;
use std::fmt;

// ISA notes:
//
// * x86 and ARM use 16-byte SIMD registers, and have an instruction which performs a 64x64 -> 128
// multipy on chosen halves of two registers.
//
// * s390x and ppc64 have 16-byte SIMD registers, and a "parallel multiply then horizontal add"
// instruction.
//
// * SPARC uses 64-bit integer registers and has multiply and multiply-high-word instructions; it
// also has multi-precision XMPMUL and XMONTMUL instructions that we may or may not be able to
// profitably use.
//
// * MIPS: no support.

/// A pair of 64-bit values with 16-byte alignment (we don't need the rest of SIMD here).
#[repr(simd)]
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
struct Sixteen(u64, u64);

impl Sixteen {
    #[inline(always)]
    fn mul(self, lix: u8, right: Sixteen, rix: u8) -> Sixteen {
        let result: Sixteen;
        unsafe {
            match rix * 16 + lix {
                0 => asm!("vpclmulqdq $3,$2,$1,$0":"=Y"(result):"Y"(self),"Y"(right),"i"(0)),
                1 => asm!("vpclmulqdq $3,$2,$1,$0":"=Y"(result):"Y"(self),"Y"(right),"i"(1)),
                16 => asm!("vpclmulqdq $3,$2,$1,$0":"=Y"(result):"Y"(self),"Y"(right),"i"(16)),
                17 => asm!("vpclmulqdq $3,$2,$1,$0":"=Y"(result):"Y"(self),"Y"(right),"i"(17)),
                _ => unreachable!(),
            }
        }
        result
    }

    #[inline]
    fn xor(self, right: Sixteen) -> Sixteen {
        //Sixteen(self.0 ^ right.0, self.1 ^ right.1)
        let result: Sixteen;
        unsafe {
            asm!("vpxor $2,$1,$0":"=Y"(result):"Y"(self),"Y"(right));
        }
        result
    }

    #[inline]
    fn align(self, right: Sixteen) -> Sixteen {
        Sixteen(self.1, right.0)
    }
}

/// An element of the field GF(2^255).
#[derive(Copy, Clone)]
pub struct FE(Sixteen, Sixteen);

impl FE {
    #[inline]
    pub const fn from_words(low: u64, midlow: u64, midhigh: u64, high: u64) -> FE {
        FE(Sixteen(low, midlow), Sixteen(midhigh, high))
    }

    pub fn from_int(low: usize) -> FE {
        FE::from_words(low as u64, 0, 0, 0)
    }

    #[inline]
    pub fn one() -> FE {
        FE::from_words(1, 0, 0, 0)
    }

    #[inline]
    pub fn zero() -> FE {
        FE::from_words(0, 0, 0, 0)
    }

    #[inline]
    pub fn to_words(self) -> (u64, u64, u64, u64) {
        if (self.1 .1 >> 63) != 0 {
            (
                self.0 .0 ^ 0x2D,
                self.0 .1,
                self.1 .0,
                self.1 .1 ^ (1 << 63),
            )
        } else {
            (self.0 .0, self.0 .1, self.1 .0, self.1 .1)
        }
    }

    #[inline]
    pub fn square(self) -> FE {
        // initial product (upper half and diagonals)
        let prod0 = self.0.mul(0, self.0, 0);
        let prod2 = self.0.mul(1, self.0, 1);
        let prod4 = self.1.mul(0, self.1, 0);
        let prod6 = self.1.mul(1, self.1, 1);

        // reduce once
        let modulus = Sixteen(0x5A, 0);
        let rdiag0 = prod0.xor(prod4.mul(0, modulus, 0));
        let rdiag1 = prod4.mul(1, modulus, 0);
        let rdiag2 = prod2.xor(prod6.mul(0, modulus, 0));
        let rdiag3 = prod6.mul(1, modulus, 0);

        // reduce twice
        let rrdiag0 = rdiag0.xor(rdiag3.mul(1, modulus, 0));
        let rrdiag3 = Sixteen(rdiag3.0, 0);

        let rrprod0 = rrdiag0.xor(Sixteen(0, 0).align(rdiag1));
        let rrprod2 = rdiag2.xor(rdiag1.align(rrdiag3));

        FE(rrprod0, rrprod2)
    }

    pub fn invert(self) -> FE {
        assert!(self != FE::zero());
        let mut tmp = self;
        for _ in 0..253 {
            tmp = tmp.square() * self;
        }
        tmp.square()
    }

    // "Montgomery's trick"
    pub fn batch_invert(elems: &mut [FE]) {
        let mut partials = Vec::new();
        let mut all = FE::one();
        for e in &*elems {
            partials.push(all);
            all *= *e;
        }
        all = all.invert();
        for i in (0..elems.len()).rev() {
            let old = elems[i];
            elems[i] = all * partials[i];
            all *= old;
        }
    }

    pub fn pow(self, mut exp: usize) -> FE {
        let mut base = self;
        let mut acc = FE::one();

        while exp > 0 {
            if (exp & 1) != 0 {
                acc *= base;
            }

            exp /= 2;
            base = base.square();
        }

        acc
    }

    pub const fn dimension() -> usize {
        255
    }

    pub fn degree(self) -> i32 {
        match self.to_words() {
            (0, 0, 0, 0) => -1,
            (lo, 0, 0, 0) => 63 - lo.leading_zeros() as i32,
            (_, mlo, 0, 0) => 127 - mlo.leading_zeros() as i32,
            (_, _, mhi, 0) => 191 - mhi.leading_zeros() as i32,
            (_, _, _, hi) => 255 - hi.leading_zeros() as i32,
        }
    }
}

impl Add for FE {
    type Output = FE;

    #[inline]
    fn add(self, other: FE) -> FE {
        FE(self.0.xor(other.0), self.1.xor(other.1))
    }
}

impl AddAssign for FE {
    #[inline]
    fn add_assign(&mut self, other: FE) {
        *self = *self + other;
    }
}

impl Sub for FE {
    type Output = FE;

    #[inline]
    fn sub(self, other: FE) -> FE {
        self + other
    }
}

impl SubAssign for FE {
    #[inline]
    fn sub_assign(&mut self, other: FE) {
        *self = *self - other;
    }
}

impl Mul for FE {
    type Output = FE;

    #[inline]
    fn mul(self, other: FE) -> FE {
        // initial product (upper half and diagonals)
        let diag0 = self.0.mul(0, other.0, 0);
        let diag1 = self.0.mul(1, other.0, 0).xor(self.0.mul(0, other.0, 1));
        let diag2 = self.1
            .mul(0, other.0, 0)
            .xor(self.0.mul(1, other.0, 1))
            .xor(self.0.mul(0, other.1, 0));
        let diag3 = self.1
            .mul(1, other.0, 0)
            .xor(self.1.mul(0, other.0, 1))
            .xor(self.0.mul(1, other.1, 0))
            .xor(self.0.mul(0, other.1, 1));
        let diag4 = self.1
            .mul(1, other.0, 1)
            .xor(self.1.mul(0, other.1, 0))
            .xor(self.0.mul(1, other.1, 1));
        let diag5 = self.1.mul(1, other.1, 0).xor(self.1.mul(0, other.1, 1));
        let diag6 = self.1.mul(1, other.1, 1);

        let prod4 = diag4.xor(diag3.align(diag5));
        let prod6 = diag6.xor(diag5.align(Sixteen(0, 0)));

        // reduce once
        let modulus = Sixteen(0x5A, 0);
        let rdiag0 = diag0.xor(prod4.mul(0, modulus, 0));
        let rdiag1 = diag1.xor(prod4.mul(1, modulus, 0));
        let rdiag2 = diag2.xor(prod6.mul(0, modulus, 0));
        let rdiag3 = Sixteen(diag3.0, 0).xor(prod6.mul(1, modulus, 0));

        // reduce twice
        let rrdiag0 = rdiag0.xor(rdiag3.mul(1, modulus, 0));
        let rrdiag3 = Sixteen(rdiag3.0, 0);

        let rrprod0 = rrdiag0.xor(Sixteen(0, 0).align(rdiag1));
        let rrprod2 = rdiag2.xor(rdiag1.align(rrdiag3));

        FE(rrprod0, rrprod2)
    }
}

impl MulAssign for FE {
    #[inline]
    fn mul_assign(&mut self, other: FE) {
        *self = *self * other;
    }
}

impl PartialEq for FE {
    #[inline]
    fn eq(&self, other: &FE) -> bool {
        (*self + *other).to_words() == (0, 0, 0, 0)
    }
}

impl Eq for FE {}

impl fmt::Display for FE {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.to_words() {
            (lo, 0, 0, 0) => write!(f, "{:X}", lo),
            (lo, mlo, 0, 0) => write!(f, "{:X}{:016X}", mlo, lo),
            (lo, mlo, mhi, 0) => write!(f, "{:X}{:016X}{:016X}", mhi, mlo, lo),
            (lo, mlo, mhi, hi) => write!(f, "{:X}{:016X}{:016X}{:016X}", hi, mhi, mlo, lo),
        }
    }
}

impl fmt::Debug for FE {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl FromStr for FE {
    type Err = num::ParseIntError;

    fn from_str(mut src: &str) -> Result<FE, num::ParseIntError> {
        let mut accum = FE::zero();
        let mut mult = FE::one();
        while src.len() > 0 {
            let chunk = cmp::min(src.len(), 15);
            if !src.is_char_boundary(src.len() - chunk) {
                return Err(u64::from_str_radix("!", 16).unwrap_err());
            }
            let limb = u64::from_str_radix(&src[(src.len() - chunk)..src.len()], 16)?;
            accum += mult * FE::from_words(limb, 0, 0, 0);
            mult *= FE::from_words(1 << (4 * chunk), 0, 0, 0);
            src = &src[0..(src.len() - chunk)];
        }

        Ok(accum)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test::Bencher;
    #[test]
    fn test_limb_ops() {
        assert_eq!(Sixteen(3, 5).mul(0, Sixteen(3, 5), 0), Sixteen(5, 0));
        assert_eq!(Sixteen(3, 5).mul(1, Sixteen(3, 5), 0), Sixteen(15, 0));
        assert_eq!(Sixteen(3, 5).mul(0, Sixteen(3, 5), 1), Sixteen(15, 0));
        assert_eq!(Sixteen(3, 5).mul(1, Sixteen(3, 5), 1), Sixteen(17, 0));
    }

    #[test]
    fn test_fe() {
        assert_eq!(FE::from_words(1, 2, 3, 4).to_words(), (1, 2, 3, 4));
        assert_eq!(
            FE::from_words(1, 2, 3, 0x8000000000000004).to_words(),
            (0x2C, 2, 3, 4)
        );

        assert_eq!(
            (FE::from_words(1, 2, 3, 4) + FE::from_words(8, 16, 32, 48)).to_words(),
            (9, 18, 35, 52)
        );
        assert_eq!(
            (FE::from_words(1, 2, 3, 4) - FE::from_words(8, 16, 32, 48)).to_words(),
            (9, 18, 35, 52)
        );

        assert_eq!(
            (FE::from_words(1, 0, 0, 0) * FE::from_words(1, 0, 0, 0)).to_words(),
            (1, 0, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 1, 0, 0) * FE::from_words(1, 0, 0, 0)).to_words(),
            (0, 1, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 1, 0) * FE::from_words(1, 0, 0, 0)).to_words(),
            (0, 0, 1, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 0, 1) * FE::from_words(1, 0, 0, 0)).to_words(),
            (0, 0, 0, 1)
        );
        assert_eq!(
            (FE::from_words(1, 0, 0, 0) * FE::from_words(0, 1, 0, 0)).to_words(),
            (0, 1, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 1, 0, 0) * FE::from_words(0, 1, 0, 0)).to_words(),
            (0, 0, 1, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 1, 0) * FE::from_words(0, 1, 0, 0)).to_words(),
            (0, 0, 0, 1)
        );
        assert_eq!(
            (FE::from_words(0, 0, 0, 1) * FE::from_words(0, 1, 0, 0)).to_words(),
            (0x5A, 0, 0, 0)
        );
        assert_eq!(
            (FE::from_words(1, 0, 0, 0) * FE::from_words(0, 0, 1, 0)).to_words(),
            (0, 0, 1, 0)
        );
        assert_eq!(
            (FE::from_words(0, 1, 0, 0) * FE::from_words(0, 0, 1, 0)).to_words(),
            (0, 0, 0, 1)
        );
        assert_eq!(
            (FE::from_words(0, 0, 1, 0) * FE::from_words(0, 0, 1, 0)).to_words(),
            (0x5A, 0, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 0, 1) * FE::from_words(0, 0, 1, 0)).to_words(),
            (0, 0x5A, 0, 0)
        );
        assert_eq!(
            (FE::from_words(1, 0, 0, 0) * FE::from_words(0, 0, 0, 1)).to_words(),
            (0, 0, 0, 1)
        );
        assert_eq!(
            (FE::from_words(0, 1, 0, 0) * FE::from_words(0, 0, 0, 1)).to_words(),
            (0x5A, 0, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 1, 0) * FE::from_words(0, 0, 0, 1)).to_words(),
            (0, 0x5A, 0, 0)
        );
        assert_eq!(
            (FE::from_words(0, 0, 0, 1) * FE::from_words(0, 0, 0, 1)).to_words(),
            (0, 0, 0x5A, 0)
        );

        assert_eq!(
            FE::from_words(1, 2, 3, 4) == FE::from_words(1, 2, 3, 4),
            true
        );
        assert_eq!(
            FE::from_words(1, 2, 3, 4) == FE::from_words(1, 2, 3, 5),
            false
        );

        let v = FE::from_words(11111111, 22222222, 33333333, 444444444);
        assert_eq!(v.pow(0), FE::one());
        assert_eq!(v.pow(1), v);
        assert_eq!(v.pow(4), v.square().square());
        assert_eq!(v.pow(5), v * v.square().square());

        let mut vp = v;
        for _ in 0..254 {
            assert_eq!(vp == FE::one(), false);
            assert_eq!(vp * vp == vp.square(), true);
            assert_eq!(FE::from_str(&format!("{}", vp)).unwrap(), vp);
            assert_eq!(vp.invert() * vp, FE::one());
            vp = (vp * vp) * v;
        }
        assert_eq!(vp == FE::one(), true);
    }

    #[test]
    fn test_degree() {
        assert_eq!(FE::zero().degree(), -1);
        assert_eq!(FE::one().degree(), 0);
        assert_eq!(FE::from_words(4, 0, 0, 0).degree(), 2);
        assert_eq!(FE::from_words(0, 4, 0, 0).degree(), 66);
        assert_eq!(FE::from_words(0, 0, 4, 0).degree(), 130);
        assert_eq!(FE::from_words(0, 0, 0, 4).degree(), 194);
    }

    #[test]
    fn test_batch_invert() {
        let mut a = vec![FE::from_int(2), FE::from_int(3), FE::from_int(4)];
        let b = a.iter().map(|x| x.invert()).collect::<Vec<_>>();
        FE::batch_invert(&mut a);
        assert_eq!(a, b);
    }

    #[bench]
    fn bench_seq_mul(b: &mut Bencher) {
        let mut v = FE::from_words(11111111, 22222222, 33333333, 444444444);
        let vx = FE::from_words(11111111, 55555555, 33333333, 444444444);
        b.iter(|| v = v * vx);
    }

    #[bench]
    fn bench_par_mul(b: &mut Bencher) {
        let v = FE::from_words(11111111, 22222222, 33333333, 444444444);
        let vx = FE::from_words(11111111, 55555555, 33333333, 444444444);
        let mut i = 0;
        b.iter(|| {
            i = i + 1;
            (v + FE::from_words(i, 0, 0, 0)) * vx
        });
    }

    #[bench]
    fn bench_par_sqr(b: &mut Bencher) {
        let v = FE::from_words(11111111, 22222222, 33333333, 444444444);
        let mut i = 0;
        b.iter(|| {
            i = i + 1;
            (v + FE::from_words(i, 0, 0, 0)).square()
        });
    }
}
