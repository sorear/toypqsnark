use field::FE;
use fft;
use hash;
use geom::{self, Coset};

pub struct FRIParams {
    rate: usize,
    localization: usize,
    repetitions: usize,
    challenges: usize,
    cosets: Vec<Coset>,
    small_cosets: Vec<Coset>,
}

impl FRIParams {
    pub fn new(
        mut coset: Coset,
        rate: usize,
        localization: usize,
        stop_size: usize,
        repetitions: usize,
    ) -> FRIParams {
        let mut param = FRIParams {
            rate,
            localization,
            repetitions,
            challenges: 0,
            cosets: Vec::new(),
            small_cosets: Vec::new(),
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

        param
    }

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

pub fn prover_message(param: &FRIParams, round: usize, last: &[FE], challenge: FE) -> Vec<FE> {
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
        fft::inv_additive_fft(&mut scratch, &param.small_cosets[round].generators);
        reduced[i] = geom::poly_eval(&scratch, param.cosets[round].index(i << loc) + challenge);
    }

    if round == param.challenges - 1 {
        fft::inv_additive_fft(&mut reduced, &param.cosets[round + 1].generators);
        reduced.resize(last.len() >> (loc + param.rate), FE::zero());
    }

    reduced
}

fn prf2i(key: FE, tweak: u64) -> u64 {
    hash::prf2(key, FE::from_words(tweak, 0, 0, 0)).to_words().0
}

pub fn verifier_queries(param: &FRIParams, randomness: FE) -> Vec<(usize, usize)> {
    let mut out = Vec::new();

    for i in 0..param.repetitions {
        // index generation can be changed if this becomes a problem for the embedded verifier
        let mut index = prf2i(randomness, i as u64) as usize & (param.cosets[0].size() - 1);

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

pub fn verifier_accepts(param: &FRIParams, randomness: FE, challenges: &[FE], data: &[FE]) -> bool {
    let mut data_ix = 0;
    let loc = param.localization;
    let mut scratch = Vec::new();
    scratch.resize(1 << loc, FE::zero());

    for i in 0..param.repetitions {
        let mut index = prf2i(randomness, i as u64) as usize & (param.cosets[0].size() - 1);
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
    }

    return true;
}
