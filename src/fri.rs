fn degree(fe: FE) -> i32 {
    match fe.to_words() {
        (0, 0, 0, 0) => -1,
        (lo, 0, 0, 0) => 63 - lo.leading_zeros(),
        (_, mlo, 0, 0) => 127 - mlo.leading_zeros(),
        (_, _, mhi, 0) => 191 - mhi.leading_zeros(),
        (_, _, _, hi) => 255 - hi.leading_zeros(),
    }
}

fn gauss_elim(rows: &mut [FE]) {
    for i in 0..rows.len() {
        if let Some(j) = (i..rows.len()).max_by_key(|j| degree(rows[j])) {
            rows.swap(i, j);
        }

        for j in i+1..rows.len() {
            if degree(rows[j]) == degree(rows[i]) {
                rows[j] += rows[i];
            }
        }
    }
}

#![derive(Debug,Clone)]
struct Coset {
    base: FE,
    generators: Vec<FE>,
}

impl Coset {
    fn zero_poly(&self) -> AffinePoly {
        let mut f = vec![self.base];

        for gen in &self.generators {
            // f(x) := f(x)f(g+x) = f(x)^2 + f(g)f(x)
            let mut n = f.square();
            let fg = f.eval(gen);
            for i in 0..f.0.len() {
                n.0[i] += fg * f.0[i];
            }
            f = n;
        }

        f
    }

    fn reduce(&self) -> Coset {
        let mut red = self.clone();
        gauss_elim(&mut red.generators);
        red
    }

    fn reduced_contains_point(&self, mut point: FE) -> bool {
        point += self.base;
        for g in &self.generators {
            if degree(point) == degree(g) {
                point += g;
            }
        }
        point == FE::zero()
    }

    fn reduced_contains(&self, other: &Coset) -> bool {
        self.reduced_contains_point(other.base) && other.generators.iter().all(|g| self.reduced_contains_point(g))
    }

    fn reduced_redundant(&self) -> bool {
        self.generators.last().cloned() == Some(FE::zero())
    }

    fn intersects(&self, other: &Coset) -> bool {
        let minkowski_sum = Coset {
            base: self.base + other.base,
            generators: self.generators.iter().chain(&other.generators).collect(),
        };
        minkowski_sum.reduce().reduced_contains_point(FE::zero())
    }
}

// x^0, x^1, x^2, x^4, x^8, ...
#![derive(Debug,Clone)]
struct AffinePoly(Vec<FE>);

impl AffinePoly {
    fn eval(&self, mut at: FE) -> FE {
        let acc = self.0[0];
        for coe in &self.0[1..] {
            acc += coe * at;
            at = at.square();
        }
        acc
    }

    fn square(&self) -> AffinePoly {
        let mut n = self.clone();
        n.insert(1, FE::zero());
        n
    }
}

fn eval_poly(poly: &[FE], point: FE) -> FE {
    let mut a = poly[poly.len() - 1];
    for c in poly.iter().rev() {
        a = a * point + c;
    }
    a
}

fn shift_poly(poly: &mut [FE], mut point: FE) {
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

struct FRIParams {
    rate: usize,
    localization: usize,
    stop_size: usize,
    repetitions: usize,
    challenges: usize,
    cosets: Vec<Coset>,
    small_cosets: Vec<Coset>,
}

impl FRIParams {
    fn new(coset: Coset, rate: usize, localization: usize, stop_size: usize, repetitions: usize) -> FRIParams {
        let mut param = FRIParams {
            rate, localization, stop_size, repetitions,
            challenges: 0, cosets: Vec::new(), small_cosets: Vec::new(),
        };

        // 0-challenge 1-reply is an awkward edge case
        assert!(coset.size() > stop_size && coset.size() > (localization << rate));

        loop {
            param.cosets.push(coset.clone());
            if coset.size() <= stop_size || coset.size() <= (localization << rate) {
                break;
            }

            // this construction means that cosets are adjacent in memory
            let small = Coset {
                base: coset.base,
                generators: Vec::from(&coset.generators[0..localization]),
            };
            let quot = small.zero_poly();
            coset.base = quot.eval(coset.base);
            coset.generators.drain(0..2);
            for g in &mut coset.generators {
                *g = quot.eval(*g);
            }

            param.small_cosets.push(small);
            param.challenges += 1;
        }
    }

    fn messages(&self) -> usize {
        self.challenges + 1
    }

    fn message_size(&self, message: usize) -> usize {
        if message == self.challenges {
            self.cosets[0].size() >> (message * self.localization + self.rate)
        } else {
            self.cosets[0].size() >> (message * self.localization)
        }
    }
}

fn prover_message(param: &FRIParams, round: usize, last: &[FE], challenge: FE) -> Vec<FE> {
    assert!(last.len() == param.cosets[round].size());
    let loc = param.localization;

    let mut reduced = Vec::new();
    reduced.resize(last.len() >> loc, FE::zero());

    let mut scratch = Vec::new();
    scratch.resize(1 << loc, FE::zero());

    // will be faster if the fft is unrolled for typical loc values 2-4
    // consider sending a sequence of polynomials instead to reduce verifier work
    for i in 0..reduced.len() {
        scratch.copy_from_slice(&last[i << loc..(i + 1) << loc]);
        fft::inv_affine_fft(&mut scratch, &param.small_cosets[round].generators);
        reduced[i] = poly_eval(&scratch, param.cosets[round].index(i << loc) + challenge);
    }

    if round == challenges - 1 {
        fft::inv_affine_fft(&mut reduced, &param.cosets[round + 1].generators);
        reduced.resize(reduced.len() >> param.rate);
    }

    reduced
}

fn verifier_queries(param: &FRIParam, randomness: FE) -> Vec<(usize, usize)> {
    let mut out = Vec::new();

    for i in 0..param.repetitions {
        // index generation can be changed if this becomes a problem for the embedded verifier
        let mut index = hash::prf2(randomness, i).to_words().0 & (param.cosets[0].size() - 1);

        for j in 0..param.challenges {
            index = index >> param.localization;
            for k in 0..(1 << param.localization) {
                out.push((j, (index << param.localization) + k));
            }
        }

        for j in 0..param.message_size(param.challenges) {
            out.push((param.challenges, j));
        }
    }

    out
}

fn verifier_accepts(param: &FRIParam, randomness: FE, challenges: &[FE], data: &[FE]) -> bool {
    let mut data_ix = 0;
    let loc = param.localization;
    let mut scratch = Vec::new();
    scratch.resize(1 << loc, FE::zero());

    for i in 0..param.repetitions {
        let mut index = hash::prf2(randomness, i).to_words().0 & (param.cosets[0].size() - 1);
        let mut last = None;

        for j in 0..param.challenges {
            scratch.copy_from_slice(&data[data_ix .. data_ix + (1 << loc)]);
            data_ix += 1 << loc;

            if let Some(l) = last {
                if l != scratch[index & ((1 << loc) - 1)] {
                    return false;
                }
            }

            index = index >> loc;

            inv_affine_fft(&mut scratch, &params.small_cosets[j].generators);
            last = Some(eval_poly(&scratch, challenges[j] + params.cosets[j].index(index << loc)));
        }

        let lastsz = param.message_size(param.challenges);
        if last.unwrap() != eval_poly(&data[data_ix .. (data_ix + lastsz)], params.cosets[params.challenges].index(index)) {
            return false;
        }
    }

    return true;
}
