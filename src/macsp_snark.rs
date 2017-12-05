use merkle;
use fri;
use std::cmp;
use hash;
use fft;
use field::FE;
use geom::{self, Coset};
use std::collections::HashMap;

pub struct CSP {
    pub items: Vec<Item>,
    pub coset: Coset,
    pub dont_care: Option<Coset>,
}

pub enum Item {
    Variable(String),
    Constraint(String, Expr),
}

pub enum Expr {
    Const(FE),
    Coord,
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Var(String, FE),
}

pub struct Assignment {
    pub values: HashMap<String, Vec<FE>>,
}

pub struct ParamsBuilder {
    pub csp: CSP,
    pub evaluation_coset: Coset,
    pub merkle_radix: usize,
    pub constraint_checks: usize,
    pub fri_checks: usize,
    pub inverse_rate: usize,
    pub fri_localization: usize,
    pub masked: bool,
}

#[derive(Default)]
struct VariableInfo {
    used_shifted: bool,
    index: usize,
}

struct ConstraintInfo {
    expr: Box<ExprInfo>,
    first_quotient: usize,
    quotients: usize,
}

enum ExprInfo {
    Const(FE),
    Coord,
    Add(Box<ExprInfo>, Box<ExprInfo>),
    Mul(Box<ExprInfo>, Box<ExprInfo>),
    Var(bool, usize, FE),
}

enum ExprWalk<T> {
    Const(FE),
    Coord,
    Add(T, T),
    Mul(T, T),
    Var(bool, usize, FE),
}

impl ExprInfo {
    fn walk<R, F>(&self, func: &mut F) -> R
    where
        F: FnMut(ExprWalk<R>) -> R,
    {
        let ss = match *self {
            ExprInfo::Const(fe) => ExprWalk::Const(fe),
            ExprInfo::Coord => ExprWalk::Coord,
            ExprInfo::Var(sh, ix, sv) => ExprWalk::Var(sh, ix, sv),
            ExprInfo::Add(ref l, ref r) => ExprWalk::Add(l.walk(func), r.walk(func)),
            ExprInfo::Mul(ref l, ref r) => ExprWalk::Mul(l.walk(func), r.walk(func)),
        };
        func(ss)
    }
}

#[derive(Default)]
struct CSPInfo {
    variables: HashMap<String, VariableInfo>,
    constraints: Vec<ConstraintInfo>,
    unique_shifts: Vec<FE>,
    num_shifted_vars: usize,
    num_unshifted: usize,
    max_constraint_degree: usize,
}

impl CSPInfo {
    fn analyze(&mut self, csp: &CSP) {
        // determine which variables are used shifted
        for item in &csp.items {
            match *item {
                Item::Constraint(_, ref poly) => self.check_usage(&poly),
                Item::Variable(ref name) => {
                    assert!(!self.variables.contains_key(&*name));
                    self.variables.insert(name.clone(), VariableInfo::default());
                }
            }
        }

        // assign variables to slots and translate constraints
        for item in &csp.items {
            match *item {
                Item::Constraint(_, ref poly) => {
                    let (expr_info, mut pdeg, cdeg) = self.translate_poly(&poly);
                    if cdeg > 0 {
                        assert!(
                            cdeg
                                < csp.coset.size()
                                    + csp.dont_care.as_ref().map(|c| c.size()).unwrap_or(0)
                        );
                        pdeg += 1;
                    }
                    // linear constraints are wasteful and require an edge case in ZK math
                    assert!(pdeg >= 2);
                    self.max_constraint_degree = cmp::max(self.max_constraint_degree, pdeg);

                    self.constraints.push(ConstraintInfo {
                        expr: expr_info,
                        quotients: pdeg - 1,
                        first_quotient: self.num_unshifted,
                    });
                    self.num_unshifted += pdeg - 1;
                }
                Item::Variable(ref name) => {
                    let mut vi = self.variables.get_mut(&*name).unwrap();
                    if vi.used_shifted {
                        vi.index = self.num_shifted_vars;
                        self.num_shifted_vars += 1;
                    } else {
                        vi.index = self.num_unshifted;
                        self.num_unshifted += 1;
                    }
                }
            }
        }
    }

    fn check_usage(&mut self, expr: &Expr) {
        match *expr {
            Expr::Coord => {}
            Expr::Const(_) => {}
            Expr::Add(ref l, ref r) => {
                self.check_usage(&l);
                self.check_usage(&r);
            }
            Expr::Mul(ref l, ref r) => {
                self.check_usage(&l);
                self.check_usage(&r);
            }
            Expr::Var(ref name, shift) => {
                let vi = self.variables.get_mut(&*name).unwrap();
                if shift != FE::zero() {
                    vi.used_shifted = true;
                    if !self.unique_shifts.contains(&shift) {
                        self.unique_shifts.push(shift);
                    }
                }
            }
        }
    }

    fn translate_poly(&self, expr: &Expr) -> (Box<ExprInfo>, usize, usize) {
        match *expr {
            Expr::Coord => (Box::new(ExprInfo::Coord), 0, 1),
            Expr::Const(fe) => (Box::new(ExprInfo::Const(fe)), 0, 0),
            Expr::Add(ref l, ref r) => {
                let (li, lpdeg, lcdeg) = self.translate_poly(&l);
                let (ri, rpdeg, rcdeg) = self.translate_poly(&r);
                (
                    Box::new(ExprInfo::Add(li, ri)),
                    cmp::max(lpdeg, rpdeg),
                    cmp::max(lcdeg, rcdeg),
                )
            }
            Expr::Mul(ref l, ref r) => {
                let (li, lpdeg, lcdeg) = self.translate_poly(&l);
                let (ri, rpdeg, rcdeg) = self.translate_poly(&r);
                (
                    Box::new(ExprInfo::Mul(li, ri)),
                    lpdeg + rpdeg,
                    lcdeg + rcdeg,
                )
            }
            Expr::Var(ref name, shift) => {
                let vi = self.variables.get(&*name).unwrap();
                (
                    Box::new(ExprInfo::Var(vi.used_shifted, vi.index, shift)),
                    1,
                    0,
                )
            }
        }
    }
}

impl ParamsBuilder {
    pub fn build(self) -> Params {
        let csp = self.csp;
        let masked = self.masked;
        let constraint_checks = self.constraint_checks;
        let merkle_radix = self.merkle_radix;
        let inverse_rate = self.inverse_rate;
        let fri_localization = self.fri_localization;
        let fri_checks = self.fri_checks;
        let evaluation_coset = self.evaluation_coset;

        assert!(inverse_rate.is_power_of_two());
        assert!(fri_localization.is_power_of_two());
        assert!(csp.coset.size() * inverse_rate >= fri_localization);
        assert!(evaluation_coset.size() == csp.coset.size() * inverse_rate);
        assert!(csp.dont_care.is_none()); //TODO

        let mut csp_info = CSPInfo::default();
        csp_info.analyze(&csp);

        let shifted_vars_tparam = merkle::ParamsBuilder {
            radix: merkle_radix,
            expected_queries: constraint_checks * (1 + csp_info.unique_shifts.len()),
            num_points: evaluation_coset.size(),
            page_size: 2 * masked as usize + csp_info.num_shifted_vars,
        }.build();

        let unshifted_vars_tparam = merkle::ParamsBuilder {
            radix: merkle_radix,
            expected_queries: constraint_checks,
            num_points: evaluation_coset.size(),
            page_size: 3 * masked as usize + csp_info.num_unshifted,
        }.build();

        // TODO do checks need to be independent?
        let test_tparam = merkle::ParamsBuilder {
            radix: merkle_radix,
            expected_queries: constraint_checks + fri_checks,
            num_points: evaluation_coset.size() / fri_localization,
            page_size: fri_localization,
        }.build();

        let fri_param = fri::ParamsBuilder {
            coset: evaluation_coset.clone(),
            rate: inverse_rate.trailing_zeros() as usize,
            localization: fri_localization.trailing_zeros() as usize,
            stop_size: fri_checks, // TODO
        }.build();

        assert!(fri_param.messages() >= 2);

        let mut fri_message_tparam = Vec::new();

        fri_message_tparam.push(test_tparam);

        for msg in 1..fri_param.messages() - 1 {
            fri_message_tparam.push(
                merkle::ParamsBuilder {
                    radix: merkle_radix,
                    expected_queries: fri_checks,
                    page_size: fri_localization,
                    num_points: fri_param.message_size(msg) / fri_localization,
                }.build(),
            );
        }

        let mut xor_shifts = vec![0];
        for &shift in &csp_info.unique_shifts {
            xor_shifts.push(
                evaluation_coset
                    .reverse_index(shift)
                    .expect("evaluation coset not closed under shifts"),
            );
        }

        Params {
            csp,
            fri_message_tparam,
            fri_param,
            fri_localization,
            shifted_vars_tparam,
            unshifted_vars_tparam,
            constraint_checks,
            fri_checks,
            evaluation_coset,
            csp_info,
            masked,
            xor_shifts,
        }
    }
}

pub struct Params {
    csp: CSP,
    csp_info: CSPInfo,
    evaluation_coset: Coset,
    xor_shifts: Vec<usize>,
    masked: bool,
    shifted_vars_tparam: merkle::Params,
    unshifted_vars_tparam: merkle::Params,
    fri_localization: usize,
    fri_param: fri::Params,
    // [0] is the test function
    fri_message_tparam: Vec<merkle::Params>,
    constraint_checks: usize,
    fri_checks: usize,
}

impl Params {
    pub fn proof_size(&self) -> usize {
        let mut len = 0;
        len += self.shifted_vars_tparam.root_elements();
        len += self.unshifted_vars_tparam.root_elements();

        for i in 0..(self.fri_param.messages() - 1) {
            len += self.fri_message_tparam[i].root_elements();
        }

        len += self.fri_param.message_size(self.fri_param.messages() - 1);

        len += self.shifted_vars_tparam.path_elements() * self.constraint_checks
            * self.xor_shifts.len();
        len += self.unshifted_vars_tparam.path_elements() * self.constraint_checks;
        len += self.fri_message_tparam[0].path_elements() * self.constraint_checks;

        for message in 0..(self.fri_param.messages() - 1) {
            len += self.fri_message_tparam[message].path_elements() * self.fri_checks;
        }

        len
    }

    pub fn verify(&self, proof: &[FE]) -> bool {
        self.verify_catch(proof).is_some()
    }

    pub fn verify_catch(&self, mut proof: &[FE]) -> Option<()> {
        let mut commitments = Vec::new();
        assert!(proof.len() == self.proof_size());

        let (shifted_root, shifted_commit) = self.shifted_vars_tparam.read_root(&mut proof);
        commitments.push(shifted_commit);
        let (unshift_root, unshift_commit) = self.unshifted_vars_tparam.read_root(&mut proof);
        commitments.push(unshift_commit);

        let linear_challenge = hash::hash1(&commitments);

        let mut message_roots = Vec::new();
        let mut message_challenges = Vec::new();

        for i in 0..(self.fri_param.messages() - 1) {
            let (message_root, message_commit) = self.fri_message_tparam[i].read_root(&mut proof);
            commitments.push(message_commit);
            message_roots.push(message_root);
            message_challenges.push(hash::hash1(&commitments));
        }

        // last FRI message sent in full
        let fri_last_size = self.fri_param.message_size(self.fri_param.messages() - 1);
        let (fri_last, nproof) = proof.split_at(fri_last_size);
        proof = nproof;
        commitments.extend_from_slice(&fri_last);

        let final_challenge = hash::hash1(&commitments);

        // FRI-QUERY

        for query in 0..self.fri_checks {
            let point = hash::prf2i(final_challenge, query) & (self.evaluation_coset.size() - 1);

            let mut picked_fes = Vec::new();
            let mut picked_coords = Vec::new();

            let mut index = point;
            for message in 0..(self.fri_param.messages() - 1) {
                index /= self.fri_localization;
                let page = self.fri_message_tparam[message].read_path(
                    &message_roots[message],
                    index,
                    &mut proof,
                )?;

                picked_fes.extend_from_slice(&page);
                picked_coords.extend(
                    (0..self.fri_localization)
                        .map(|i| (message, index * self.fri_localization + i)),
                );
            }

            picked_fes.extend_from_slice(&fri_last);
            picked_coords.extend((0..fri_last.len()).map(|i| (self.fri_param.messages() - 1, i)));

            assert_eq!(picked_coords, fri::verifier_queries(&self.fri_param, point));
            if !fri::verifier_accepts(&self.fri_param, point, &message_challenges, &picked_fes) {
                return None;
            }
        }

        // QUERY phase for agreement betwixt polynomials and the test function

        for query in 0..self.constraint_checks {
            let point = hash::prf2i(final_challenge, query + self.fri_checks)
                & (self.evaluation_coset.size() - 1);

            let mut shifted_pages = Vec::new();
            for &shift_amt in &self.xor_shifts {
                let page = self.shifted_vars_tparam.read_path(
                    &shifted_root,
                    point ^ shift_amt,
                    &mut proof,
                )?;
                shifted_pages.push(page);
            }

            let unshifted_page =
                self.unshifted_vars_tparam
                    .read_path(&unshift_root, point, &mut proof)?;

            let test_page = self.fri_message_tparam[0].read_path(
                &message_roots[0],
                point / self.fri_localization,
                &mut proof,
            )?;

            // check constraints using quotients
            let point_eval = self.evaluation_coset.index(point);
            let zero_poly = self.csp.coset.zero_poly().eval(point_eval);

            for constraint in &self.csp_info.constraints {
                let polyval = self.eval_constraint(
                    &constraint.expr,
                    point_eval,
                    &unshifted_page,
                    &shifted_pages,
                );
                let mut quotient = FE::zero();
                for i in 0..constraint.quotients {
                    quotient *= point_eval.pow(self.csp.coset.size());
                    quotient += unshifted_page[constraint.first_quotient + i];
                }
                if quotient * zero_poly != polyval {
                    return None;
                }
            }

            // check that the test is a linear combination
            // the last 2 in each page are the merkle mask if used, don't add them
            let mut test = FE::zero();
            let mut mask_index = 0;
            let skip = 2 * self.masked as usize;

            for &fe in &unshifted_page[..unshifted_page.len() - skip] {
                test += hash::prf2(linear_challenge, FE::from_int(mask_index)) * fe;
                mask_index += 1;
            }

            for page in &shifted_pages {
                for &fe in &page[..page.len() - skip] {
                    test += hash::prf2(linear_challenge, FE::from_int(mask_index)) * fe;
                    mask_index += 1;
                }
            }

            if test != test_page[point % self.fri_localization] {
                return None;
            }
        }

        return Some(());
    }

    fn eval_constraint(
        &self,
        expr: &ExprInfo,
        point: FE,
        unshifted: &[FE],
        shifted: &[Vec<FE>],
    ) -> FE {
        match *expr {
            ExprInfo::Const(fe) => fe,
            ExprInfo::Coord => point,
            ExprInfo::Add(ref l, ref r) => {
                self.eval_constraint(&l, point, unshifted, shifted)
                    + self.eval_constraint(&r, point, unshifted, shifted)
            }
            ExprInfo::Mul(ref l, ref r) => {
                self.eval_constraint(&l, point, unshifted, shifted)
                    * self.eval_constraint(&r, point, unshifted, shifted)
            }
            ExprInfo::Var(false, index, _) => unshifted[index],
            ExprInfo::Var(true, index, shift) if shift == FE::zero() => shifted[0][index],
            ExprInfo::Var(true, index, shift) => {
                let shift_ix = self.csp_info
                    .unique_shifts
                    .iter()
                    .position(|s| *s == shift)
                    .unwrap();
                shifted[shift_ix + 1][index]
            }
        }
    }

    pub fn prove(&self, assignment: &Assignment) -> Vec<FE> {
        let mut proof = Vec::new();

        if self.masked {
            unimplemented!();
        }

        let poly_size = self.evaluation_coset.size();
        let ref evaluation_coset = self.evaluation_coset;
        let ref coset = self.csp.coset;

        let mut shift_poly = Vec::new();
        let shift_page_size = self.csp_info.num_shifted_vars;
        shift_poly.resize(poly_size * shift_page_size, FE::zero());

        let mut unshift_poly = Vec::new();
        let unshift_page_size = self.csp_info.num_unshifted;
        unshift_poly.resize(poly_size * unshift_page_size, FE::zero());

        // create variable polynomials

        for (name, vec) in &assignment.values {
            let vi = self.csp_info.variables.get(&*name).unwrap();
            let mut work = vec.clone();
            assert!(vec.len() == coset.size());
            fft::inv_additive_fft(&mut work, &coset.generators);
            geom::poly_shift(&mut work, coset.base + evaluation_coset.base);
            work.resize(poly_size, FE::zero());
            fft::additive_fft(&mut work, poly_size, &evaluation_coset.generators);

            if vi.used_shifted {
                for i in 0..poly_size {
                    shift_poly[shift_page_size * i + vi.index] = work[i];
                }
            } else {
                for i in 0..poly_size {
                    unshift_poly[unshift_page_size * i + vi.index] = work[i];
                }
            }
        }

        // create constraint polynomials

        if coset.intersects(&evaluation_coset) {
            unimplemented!();
        }

        let mut zero_cancel = Vec::new();
        for i in 0..poly_size {
            zero_cancel.push(coset.zero_poly().eval(evaluation_coset.index(i)));
        }
        FE::batch_invert(&mut zero_cancel);

        for constraint in &self.csp_info.constraints {
            let poly = constraint.expr.walk::<Vec<FE>, _>(&mut |w| match w {
                ExprWalk::Const(fe) => vec![fe; poly_size],
                ExprWalk::Coord => (0..poly_size).map(|i| evaluation_coset.index(i)).collect(),
                ExprWalk::Var(shifted, ix, sval) => {
                    let sxor = evaluation_coset.reverse_index(sval).unwrap();
                    let mut result = Vec::new();
                    for i in 0..poly_size {
                        result.push(if shifted {
                            shift_poly[shift_page_size * (sxor ^ i) + ix]
                        } else {
                            unshift_poly[unshift_page_size * i + ix]
                        });
                    }
                    result
                }
                ExprWalk::Add(l, r) => l.into_iter().zip(r).map(|(a, b)| a + b).collect(),
                ExprWalk::Mul(l, r) => l.into_iter().zip(r).map(|(a, b)| a * b).collect(),
            });

            if constraint.quotients > 1 {
                unimplemented!();
            } else {
                for i in 0..poly_size {
                    unshift_poly[unshift_page_size * i + constraint.first_quotient] =
                        poly[i] * zero_cancel[i];
                }
            }
        }

        // transmit merkle roots
        let mut commitments = Vec::new();

        let shift_prover = self.shifted_vars_tparam.make_tree(&shift_poly);
        commitments.push(shift_prover.emit_root(&mut proof));

        let unshift_prover = self.unshifted_vars_tparam.make_tree(&unshift_poly);
        commitments.push(unshift_prover.emit_root(&mut proof));

        // generate test polynomial

        let linear_challenge = hash::hash1(&commitments);
        let linear_skip = 2 * self.masked as usize;
        let mut linear_comb = Vec::new();
        for i in 0..(unshift_page_size + shift_page_size * self.xor_shifts.len()) {
            linear_comb.push(hash::prf2(linear_challenge, FE::from_int(i)));
        }

        let mut test_poly = Vec::new();
        for i in 0..poly_size {
            let mut comb = FE::zero();
            let mut index = 0;

            let ui = unshift_page_size * i;
            for &fe in &unshift_poly[ui..ui + unshift_page_size - linear_skip] {
                comb += fe * linear_comb[index];
                index += 1;
            }

            for &shift in &self.xor_shifts {
                let si = shift_page_size * (i ^ shift);
                for &fe in &shift_poly[si..si + shift_page_size - linear_skip] {
                    comb += fe * linear_comb[index];
                    index += 1;
                }
            }

            test_poly.push(comb);
        }

        let mut fri_messages = vec![test_poly];
        let mut fri_message_provers = Vec::new();
        fri_message_provers.push(self.fri_message_tparam[0].make_tree(&fri_messages[0]));
        commitments.push(fri_message_provers[0].emit_root(&mut proof));

        // FRI-COMMIT

        for n in 1..self.fri_param.messages() {
            let fri_next = fri::prover_message(
                &self.fri_param,
                n - 1,
                &fri_messages[n - 1],
                hash::hash1(&commitments),
            );
            if n == self.fri_param.messages() - 1 {
                proof.extend_from_slice(&fri_next);
                commitments.extend_from_slice(&fri_next);
            } else {
                fri_message_provers.push(self.fri_message_tparam[n].make_tree(&fri_next));
                commitments.push(fri_message_provers[n].emit_root(&mut proof));
            }
            fri_messages.push(fri_next);
        }

        // FRI-QUERY

        let final_challenge = hash::hash1(&commitments);
        for query in 0..self.fri_checks {
            let mut index =
                hash::prf2i(final_challenge, query) & (self.evaluation_coset.size() - 1);

            for message in 0..(self.fri_param.messages() - 1) {
                index /= self.fri_localization;
                fri_message_provers[message].emit_path(&fri_messages[message], index, &mut proof);
            }
        }

        // consistency checks

        for query in 0..self.constraint_checks {
            let point = hash::prf2i(final_challenge, query + self.fri_checks)
                & (self.evaluation_coset.size() - 1);

            for &shift_amt in &self.xor_shifts {
                shift_prover.emit_path(&shift_poly, point ^ shift_amt, &mut proof);
            }

            unshift_prover.emit_path(&unshift_poly, point, &mut proof);
            fri_message_provers[0].emit_path(
                &fri_messages[0],
                point / self.fri_localization,
                &mut proof,
            );
        }

        return proof;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_csp_complete() {
        let coset1 = Coset::affine(
            FE::from_int(1),
            (1..5).map(|i| FE::from_int(1 << i)).collect(),
        );
        let coset2 = Coset::linear((1..8).map(|i| FE::from_int(1 << i)).collect());
        let p = ParamsBuilder {
            csp: CSP {
                items: vec![
                    Item::Variable("x".to_owned()),
                    Item::Constraint(
                        "x01".to_owned(),
                        Expr::Mul(
                            Box::new(Expr::Var("x".to_owned(), FE::from_int(2))),
                            Box::new(Expr::Add(
                                Box::new(Expr::Const(FE::one())),
                                Box::new(Expr::Var("x".to_owned(), FE::from_int(2))),
                            )),
                        ),
                    ),
                ],
                coset: coset1,
                dont_care: None,
            },
            evaluation_coset: coset2,
            merkle_radix: 4,
            constraint_checks: 50,
            fri_checks: 50,
            inverse_rate: 8,
            fri_localization: 2,
            masked: false,
        }.build();
        let asn = Assignment {
            values: vec![
                (
                    "x".to_owned(),
                    (0..16i8)
                        .map(|i| FE::from_int(i.count_ones() as usize % 2))
                        .collect(),
                ),
            ].into_iter()
                .collect(),
        };
        let proof = p.prove(&asn);
        let accepts = p.verify(&proof);
        assert!(accepts);
    }
}
