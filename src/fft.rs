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
fn additive_fft(poly: &mut [FE], mut poly_size_hint: usize, beta: &[FE]) {
    assert!(poly.len().is_power_of_two());
    assert!(poly.len().trailing_zeros() as usize == beta.len());
    assert!(poly_size_hint <= poly.len());
    poly_size_hint += poly_size_hint & 1;

    if beta.len() == 0 {
        return;
    }

    if beta.len() == 1 {
        // poly[0] is already the constant term; replace poly[1] with poly[beta[0]]
        poly[1] = poly[0] + beta[0] * poly[1];
        return;
    }

    let b_high = beta[beta.len() - 1];
    let b_high_inv = b_high.invert();

    let mut gamma = Vec::new();
    let mut delta = Vec::new();
    let mut gamma_psum = Vec::new();
    let half_len = poly.len() >> 1;

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

    // replace poly (f) with g s.t. g(x) = f(x*b_high)
    let mut b_pow = FE::one();
    for i in 0..poly_size_hint {
        poly[i] *= b_pow;
        b_pow *= b_high;
    }

    taylor_expand(&mut poly[0..poly_size_hint]);
    // poly is now (g0,g1) but interleaved

    // de-interleave
    let scratch = Vec::from(&*poly);
    for i in 0..half_len {
        poly[i] = scratch[2 * i];
    }
    for i in 0..half_len {
        poly[i + half_len] = scratch[2 * i + 1];
    }
    // poly is now g_0, g_1

    additive_fft(&mut poly[..half_len], (poly_size_hint + 1) >> 1, &delta);
    additive_fft(&mut poly[half_len..], (poly_size_hint + 1) >> 1, &delta);

    // poly is now u_0, v_0
    let mut g_i = FE::zero();
    for i in 0..half_len {
        if i > 0 {
            g_i += gamma_psum[i.trailing_zeros() as usize];
        }
        poly[i] += poly[half_len + i] * g_i;
        poly[half_len + i] += poly[i];
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
            additive_fft(&mut poly, 1 << size, &beta);
            quadratic_afft(&mut p2, &beta);
            assert_eq!(poly, p2);
        }
    }
}
