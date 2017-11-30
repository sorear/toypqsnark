// Shuhong Gao and Todd Mateer. Additive fast fourier transforms over finite fields.
// IEEE Trans. Inf. Theor., 56(12):6265–6272, December 2010.

use field::FE;

fn taylor_expand(poly: &mut [FE]) {
    // t is fixed to 2
    assert!((poly.len() % 2) == 0);

    if poly.len() <= 2 {
        return;
    }

    let two_k = poly.len().next_power_of_two() >> 2;

    // f_0 = poly[0..2*two_k]
    // f_1 = poly[2*two_k..3*two_k]
    // f_2 = poly[3*two_k..4*two_k]
    // 2*two_k < poly.len() <= 4*two_k

    // replace f_1&f_2 with g_1 = f_1 + f_2 + f_2 * x^two_k
    for i in 0..two_k {
        if 3 * two_k + i < poly.len() {
            poly[2 * two_k + i] += poly[3 * two_k + i];
        }
    }

    // replace f_0 with g_0 = f_0 + (f_1 + f_2) * x^two_k
    for i in 0..two_k {
        if 2 * two_k + i < poly.len() {
            poly[two_k + i] += poly[2 * two_k + i];
        }
    }

    taylor_expand(&mut poly[0..2 * two_k]);
    taylor_expand(&mut poly[2 * two_k..]);
}

fn inv_taylor_expand(poly: &mut [FE]) {
    assert!((poly.len() % 2) == 0);

    if poly.len() <= 2 {
        return;
    }

    let two_k = poly.len().next_power_of_two() >> 2;

    inv_taylor_expand(&mut poly[0..2 * two_k]);
    inv_taylor_expand(&mut poly[2 * two_k..]);

    for i in 0..two_k {
        if 2 * two_k + i < poly.len() {
            poly[two_k + i] += poly[2 * two_k + i];
        }
    }

    for i in 0..two_k {
        if 3 * two_k + i < poly.len() {
            poly[2 * two_k + i] += poly[3 * two_k + i];
        }
    }
}

// evaluate poly at a number of points equal to its size; set poly_size_hint to the length of the
// leading nonzero segment of poly (remainder _must_ still be zeroed); evaluation points are
// obtained by taking the dot product of the index in binary with beta
pub fn additive_fft(poly: &mut [FE], poly_size_hint: usize, beta: &[FE]) {
    let ctx = setup_afft(poly, poly_size_hint, beta, false);
    let mut scratch = Vec::new();
    scratch.resize(poly.len() >> 2, FE::zero());
    do_afft(&ctx, 0, poly, &mut scratch);
}

pub fn inv_additive_fft(poly: &mut [FE], beta: &[FE]) {
    let ctx = setup_afft(poly, poly.len(), beta, true);
    let mut scratch = Vec::new();
    scratch.resize(poly.len(), FE::zero());
    do_inv_afft(&ctx, 0, poly, &mut scratch);
}

#[derive(Default)]
struct AFFTContext {
    levels: Vec<AFFTLevel>,
}

struct AFFTLevel {
    poly_size_hint: usize,
    b_high: FE,
    b_high_inv: FE,
    beta: Vec<FE>,
    gamma_psum: Vec<FE>,
    beta_powers: Vec<FE>,
}

fn setup_afft(poly: &[FE], mut poly_size_hint: usize, inbeta: &[FE], rev: bool) -> AFFTContext {
    assert!(poly.len().is_power_of_two());
    assert!(poly.len().trailing_zeros() as usize == inbeta.len());
    assert!(poly_size_hint <= poly.len());
    poly_size_hint += poly_size_hint & 1;

    let mut ctx = AFFTContext::default();

    let mut beta = Vec::from(&*inbeta);
    loop {
        let b_high = beta.last().cloned().unwrap_or(FE::zero());
        let b_high_inv = b_high.invert();

        if beta.len() <= 1 {
            ctx.levels.push(AFFTLevel {
                poly_size_hint,
                b_high,
                b_high_inv,
                beta: beta,
                gamma_psum: Vec::new(),
                beta_powers: Vec::new(),
            });
            break;
        }

        let mut gamma = Vec::new();
        let mut delta = Vec::new();
        let mut gamma_psum = Vec::new();

        for i in 0..beta.len() - 1 {
            gamma.push(beta[i] * b_high_inv);
            delta.push(gamma[i].square() - gamma[i]);
            if i == 0 {
                gamma_psum.push(gamma[i]);
            } else {
                let glast = gamma_psum[i - 1];
                gamma_psum.push(gamma[i] + glast);
            }
        }

        let mut beta_powers = Vec::new();

        // only generate these if they are likely to fit in L2
        // faster to generate on the fly otherwise

        if poly_size_hint <= 2048 {
            let b_step = if rev { b_high_inv } else { b_high };
            let mut power = FE::one();
            for _ in 0..poly_size_hint {
                beta_powers.push(power);
                power *= b_step;
            }
        }

        ctx.levels.push(AFFTLevel {
            poly_size_hint,
            b_high,
            b_high_inv,
            beta,
            gamma_psum,
            beta_powers,
        });
        beta = delta;
        poly_size_hint = (poly_size_hint + 1) >> 1;
    }

    ctx
}

fn do_afft(ctx: &AFFTContext, level: usize, poly: &mut [FE], scratch: &mut [FE]) {
    let li = &ctx.levels[level];
    if li.beta.len() == 0 {
        return;
    }

    if li.beta.len() == 1 {
        // poly[0] is already the constant term; replace poly[1] with poly[beta[0]]
        poly[1] = poly[0] + li.beta[0] * poly[1];
        return;
    }

    let half_len = poly.len() >> 1;

    // replace poly (f) with g s.t. g(x) = f(x*b_high)
    if li.beta_powers.len() > 0 {
        assert_eq!(li.beta_powers.len(), li.poly_size_hint);
        for i in 0..li.poly_size_hint {
            poly[i] *= li.beta_powers[i];
        }
    } else {
        let mut b_pow = FE::one();
        for i in 0..li.poly_size_hint {
            poly[i] *= b_pow;
            b_pow *= li.b_high;
        }
    }

    taylor_expand(&mut poly[0..li.poly_size_hint]);
    // poly is now (g0,g1) but interleaved

    // de-interleave
    for i in 0..half_len >> 1 {
        scratch[i] = poly[2 * i + 1];
    }
    for i in 0..half_len {
        poly[i] = poly[2 * i];
    }
    for i in 0..half_len >> 1 {
        poly[half_len * 2 - 1 - i] = poly[2 * (half_len - 1 - i) + 1];
    }
    poly[half_len..half_len + (half_len >> 1)].copy_from_slice(&scratch[..half_len >> 1]);

    // poly is now g_0, g_1

    do_afft(ctx, level + 1, &mut poly[..half_len], scratch);
    do_afft(ctx, level + 1, &mut poly[half_len..], scratch);

    // poly is now u_0, v_0
    let mut g_i = FE::zero();
    for i in 0..half_len {
        if i > 0 {
            g_i += li.gamma_psum[i.trailing_zeros() as usize];
        }
        poly[i] += poly[half_len + i] * g_i;
        poly[half_len + i] += poly[i];
    }
}

fn do_inv_afft(ctx: &AFFTContext, level: usize, poly: &mut [FE], scratch: &mut [FE]) {
    let li = &ctx.levels[level];
    if li.beta.len() == 0 {
        return;
    }

    if li.beta.len() == 1 {
        // poly[0] is already the constant term; replace poly[1] with poly[beta[0]]
        poly[1] = (poly[0] + poly[1]) * li.b_high_inv;
        return;
    }

    let half_len = poly.len() >> 1;

    let mut g_i = FE::zero();
    for i in 0..half_len {
        if i > 0 {
            g_i += li.gamma_psum[i.trailing_zeros() as usize];
        }
        poly[half_len + i] -= poly[i];
        poly[i] -= poly[half_len + i] * g_i;
    }
    // poly is now u_0, v_0

    do_inv_afft(ctx, level + 1, &mut poly[..half_len], scratch);
    do_inv_afft(ctx, level + 1, &mut poly[half_len..], scratch);

    // poly is now g_0, g_1
    // re-interleave
    scratch[0..half_len * 2].copy_from_slice(&*poly);

    for i in 0..half_len {
        poly[2 * i] = scratch[i];
        poly[2 * i + 1] = scratch[half_len + i];
    }

    // poly is now (g0,g1) but interleaved

    inv_taylor_expand(&mut poly[0..li.poly_size_hint]);

    // replace poly (f) with g s.t. g(x) = f(x*b_high)
    if li.beta_powers.len() > 0 {
        assert_eq!(li.beta_powers.len(), li.poly_size_hint);
        for i in 0..li.poly_size_hint {
            poly[i] *= li.beta_powers[i];
        }
    } else {
        let mut b_pow = FE::one();
        for i in 0..li.poly_size_hint {
            poly[i] *= b_pow;
            b_pow *= li.b_high_inv;
        }
    }
}

#[cfg(test)]
fn quadratic_afft(poly: &mut [FE], beta: &[FE]) {
    let scratch = Vec::from(&*poly);

    for i in 0..poly.len() {
        let mut coord = FE::zero();
        for j in 0..beta.len() {
            if (i & (1 << j)) != 0 {
                coord += beta[j];
            }
        }

        let mut cpow = FE::one();
        let mut acc = FE::zero();
        for j in 0..poly.len() {
            acc += scratch[j] * cpow;
            cpow *= coord;
        }

        poly[i] = acc;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use hash;

    #[test]
    fn test_afft() {
        for size in 0..4 {
            let mut poly = hash::testdata(1 << size, 0);
            let beta = hash::testdata(size, 1 << size);
            let mut p2 = poly.clone();
            let mut p3 = poly.clone();
            additive_fft(&mut poly, 1 << size, &beta);
            quadratic_afft(&mut p2, &beta);
            assert_eq!(poly, p2);
            inv_additive_fft(&mut poly, &beta);
            assert_eq!(poly, p3);
        }
    }
}
