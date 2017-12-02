use field::FE;

// x^0, x^1, x^2, x^4, x^8, ...
#[derive(Debug, Clone)]
pub struct AffinePoly(Vec<FE>);

impl AffinePoly {
    pub fn eval(&self, mut at: FE) -> FE {
        let mut acc = self.0[0];
        for coe in &self.0[1..] {
            acc += *coe * at;
            at = at.square();
        }
        acc
    }

    fn square(&self) -> AffinePoly {
        let mut n = self.clone();
        n.0.insert(1, FE::zero());
        for coe in &mut n.0 {
            *coe = coe.square();
        }
        n
    }
}

fn gauss_elim(rows: &mut [FE]) {
    for i in 0..rows.len() {
        if let Some(j) = (i..rows.len()).max_by_key(|&j| rows[j].degree()) {
            rows.swap(i, j);
        }

        for j in i + 1..rows.len() {
            if rows[j].degree() == rows[i].degree() {
                rows[j] += rows[i];
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Coset {
    pub base: FE,
    pub generators: Vec<FE>,
}

impl Coset {
    pub fn linear(gen: Vec<FE>) -> Coset {
        Coset::affine(FE::zero(), gen)
    }

    pub fn affine(base: FE, generators: Vec<FE>) -> Coset {
        Coset { base, generators }
    }

    pub fn zero_poly(&self) -> AffinePoly {
        let mut f = AffinePoly(vec![self.base, FE::one()]);

        for &gen in &self.generators {
            // f(x) := f(x)f(g+x) = (f(x)+f(g)+f(0))f(x)
            let mut n = f.square();
            let fg0 = f.eval(gen) + f.eval(FE::zero());
            for i in 0..f.0.len() {
                n.0[i] += fg0 * f.0[i];
            }
            f = n;
        }

        f
    }

    pub fn size(&self) -> usize {
        assert!(self.generators.len() < 0usize.count_zeros() as usize);
        1 << self.generators.len()
    }

    // an iterator could be faster
    pub fn index(&self, ix: usize) -> FE {
        let mut coord = self.base;
        assert!(ix < self.size());
        for j in 0..self.generators.len() {
            if (ix & (1 << j)) != 0 {
                coord += self.generators[j];
            }
        }
        coord
    }

    fn reduce(&self) -> Coset {
        let mut red = self.clone();
        gauss_elim(&mut red.generators);
        red
    }

    fn reduced_contains_point(&self, mut point: FE) -> bool {
        point += self.base;
        for &g in &self.generators {
            if point.degree() == g.degree() {
                point += g;
            }
        }
        point == FE::zero()
    }

    pub fn contains(&self, other: &Coset) -> bool {
        let r = self.reduce();
        r.reduced_contains_point(other.base)
            && other
                .generators
                .iter()
                .all(|g| r.reduced_contains_point(*g))
    }

    pub fn redundant(&self) -> bool {
        self.reduce().generators.last().cloned() == Some(FE::zero())
    }

    pub fn intersects(&self, other: &Coset) -> bool {
        let minkowski_sum = Coset {
            base: self.base + other.base,
            generators: self.generators
                .iter()
                .chain(&other.generators)
                .cloned()
                .collect(),
        };
        minkowski_sum.reduce().reduced_contains_point(FE::zero())
    }
}

pub fn poly_eval(poly: &[FE], point: FE) -> FE {
    let mut a = poly[poly.len() - 1];
    for c in 0..(poly.len() - 1) {
        a = a * point + poly[poly.len() - 2 - c];
    }
    a
}

pub fn poly_shift(poly: &mut [FE], mut point: FE) {
    let mut block = 1;
    while block < poly.len() {
        let mut ix = 0;
        while ix + block < poly.len() {
            poly[ix] += point * poly[ix + block];
            ix += 1;
            ix += ix & block;
        }
        block <<= 1;
        point = point.square();
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use hash;

    #[test]
    fn test_cosets() {
        let c3 = Coset::affine(hash::testdata(1, 0)[0], hash::testdata(3, 1));

        assert!(c3.size() == 8);
        assert!(c3.index(0) == c3.base);
        assert!(c3.index(5) == c3.base + c3.generators[0] + c3.generators[2]);

        assert!(c3.zero_poly().eval(FE::zero()) != FE::zero());
        for i in 0..8 {
            assert!(c3.zero_poly().eval(c3.index(i)) == FE::zero());
        }

        assert!(!c3.redundant());
        assert!(Coset::linear(vec![c3.base, c3.base]).redundant());
        assert!(!Coset::linear(vec![FE::one(), c3.base]).redundant());
        assert!(Coset::linear(vec![FE::one(), c3.base, c3.base + FE::one()]).redundant());
    }

    #[test]
    fn test_poly() {
        let p = hash::testdata(4, 0);
        let pp = hash::testdata(1, 4)[0];
        assert_eq!(
            poly_eval(&p, pp),
            p[0] + p[1] * pp + p[2] * pp * pp + p[3] * pp * pp * pp
        );
    }
}
