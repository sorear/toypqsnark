use field::FE;
use fft;
use geom::{self, Coset};

pub struct ParamsBuilder {
    pub coset: Coset,
    pub rate: usize,
    pub localization: usize,
    pub stop_size: usize,
}

impl ParamsBuilder {
    pub fn build(self) -> Params {
        let ParamsBuilder {
            mut coset,
            rate,
            localization,
            stop_size,
        } = self;
        let mut param = Params {
            rate,
            localization,
            challenges: 0,
            cosets: Vec::new(),
            small_cosets: Vec::new(),
        };

        // 0-challenge 1-reply is an awkward edge case
        assert!(coset.size() > (1 << (localization + rate)));

        loop {
            assert!(!coset.redundant());
            param.cosets.push(coset.clone());
            if coset.size() <= (1 << (localization + rate)) {
                break;
            }

            if param.challenges >= 1 && coset.size() <= stop_size {
                break;
            }

            // this construction means that cosets are adjacent in memory
            let small = Coset {
                base: coset.base,
                generators: Vec::from(&coset.generators[0..localization]),
            };
            let quot = small.zero_poly();
            coset.base = quot.eval(coset.base);
            coset.generators.drain(0..localization);
            for g in &mut coset.generators {
                *g = quot.eval(*g) + quot.eval(FE::zero());
            }

            param.small_cosets.push(small);
            param.challenges += 1;
        }

        param
    }
}

pub struct Params {
    rate: usize,
    localization: usize,
    challenges: usize,
    cosets: Vec<Coset>,
    small_cosets: Vec<Coset>,
}

impl Params {
    pub fn messages(&self) -> usize {
        self.challenges + 1
    }

    pub fn message_size(&self, message: usize) -> usize {
        if message == self.challenges {
            self.cosets[0].size() >> (message * self.localization + self.rate)
        } else {
            self.cosets[0].size() >> (message * self.localization)
        }
    }
}

pub fn prover_message(param: &Params, round: usize, last: &[FE], challenge: FE) -> Vec<FE> {
    assert!(last.len() == param.cosets[round].size());
    assert!(!param.small_cosets[round].redundant());
    let loc = param.localization;

    let mut reduced = Vec::new();
    reduced.resize(last.len() >> loc, FE::zero());

    let mut scratch = Vec::new();
    scratch.resize(1 << loc, FE::zero());

    // will be faster if the fft is unrolled for typical loc values 2-4
    // consider sending a sequence of polynomials instead to reduce verifier work
    for i in 0..reduced.len() {
        assert!(
            param.small_cosets[round]
                .zero_poly()
                .eval(param.cosets[round].index(i << loc))
                == param.cosets[round + 1].index(i)
        );
        assert!(
            param.small_cosets[round]
                .zero_poly()
                .eval(param.cosets[round].index((i << loc) + 1))
                == param.cosets[round + 1].index(i)
        );
        scratch.copy_from_slice(&last[i << loc..(i + 1) << loc]);
        fft::inv_additive_fft(&mut scratch, &param.small_cosets[round].generators);
        reduced[i] = geom::poly_eval(&scratch, param.cosets[round].index(i << loc) + challenge);
    }

    if round == param.challenges - 1 {
        fft::inv_additive_fft(&mut reduced, &param.cosets[round + 1].generators);
        reduced.resize(last.len() >> (loc + param.rate), FE::zero());
    }

    reduced
}

pub fn verifier_queries(param: &Params, mut index: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    assert!(index <= param.cosets[0].size());

    for j in 0..param.challenges {
        index = index >> param.localization;
        for k in 0..(1 << param.localization) {
            out.push((j, (index << param.localization) + k));
        }
    }

    for j in 0..param.message_size(param.challenges) {
        out.push((param.challenges, j));
    }

    out
}

pub fn verifier_accepts(param: &Params, mut index: usize, challenges: &[FE], data: &[FE]) -> bool {
    let mut data_ix = 0;
    let loc = param.localization;
    let mut scratch = Vec::new();
    scratch.resize(1 << loc, FE::zero());
    assert!(index <= param.cosets[0].size());
    assert!(challenges.len() == param.challenges);

    let mut last = None;

    for j in 0..param.challenges {
        scratch.copy_from_slice(&data[data_ix..data_ix + (1 << loc)]);
        data_ix += 1 << loc;

        if let Some(l) = last {
            if l != scratch[index & ((1 << loc) - 1)] {
                return false;
            }
        }

        index = index >> loc;

        fft::inv_additive_fft(&mut scratch, &param.small_cosets[j].generators);
        last = Some(geom::poly_eval(
            &scratch,
            challenges[j] + param.cosets[j].index(index << loc),
        ));
    }

    let lastsz = param.message_size(param.challenges);
    if last.unwrap()
        != geom::poly_eval(
            &data[data_ix..(data_ix + lastsz)],
            param.cosets[param.challenges].index(index),
        ) {
        return false;
    }

    return true;
}

#[cfg(test)]
mod test {
    use super::*;
    use hash;

    fn prf2i(key: FE, tweak: u64) -> u64 {
        hash::prf2(key, FE::from_words(tweak, 0, 0, 0)).to_words().0
    }

    #[test]
    fn test_prover_completeness() {
        let mut poly = hash::testdata(128, 0);
        let coset = Coset::linear(hash::testdata(10, 200));
        let param = ParamsBuilder {
            coset: coset.clone(),
            rate: 3,
            localization: 1,
            stop_size: 1,
        }.build();
        let challenges = hash::testdata(param.challenges, 300);
        poly.resize(1024, FE::zero());
        fft::additive_fft(&mut poly, 1024, &coset.generators);

        let mut messages = vec![poly];
        for round in 0..param.challenges {
            let next = prover_message(&param, round, &messages[round], challenges[round]);
            messages.push(next);
        }

        let randomness = hash::testdata(1, 400)[0];
        for i in 0..500 {
            let mut index = prf2i(randomness, i as u64) as usize & (coset.size() - 1);

            let queries = verifier_queries(&param, index);
            let results = queries
                .iter()
                .map(|&(msg, ix)| messages[msg][ix])
                .collect::<Vec<_>>();
            let accepts = verifier_accepts(&param, index, &challenges, &results);
            assert!(accepts);
        }
    }
}
