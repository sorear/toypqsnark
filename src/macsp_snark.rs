use merkle;
use fri;
use std::cmp;
use hash;
use field::FE;
use geom::Coset;
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
    pub values: Vec<Vec<FE>>,
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
        }
    }
}

pub struct Params {
    csp: CSP,
    csp_info: CSPInfo,
    evaluation_coset: Coset,
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
    pub fn verify(&self, mut proof: &[FE]) -> bool {
        let mut commitments = Vec::new();

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
        let (fri_last, nproof) =
            proof.split_at(self.fri_param.message_size(self.fri_param.messages() - 1));
        proof = nproof;
        commitments.extend_from_slice(&fri_last);

        let final_challenge = hash::hash1(&commitments);

        // QUERY phase for agreement betwixt polynomials and the test function

        for query in 0..self.constraint_checks {
            let point = hash::prf2i(final_challenge, query) & (self.evaluation_coset.size() - 1);

            let mut shifted_pages = Vec::new();
            for &shift_amt in [FE::zero()].iter().chain(&self.csp_info.unique_shifts) {
                let shift_point = point ^ self.evaluation_coset.reverse_index(shift_amt).unwrap();
                match self.shifted_vars_tparam
                    .read_path(&shifted_root, shift_point, &mut proof)
                {
                    Some(page) => shifted_pages.push(page),
                    None => return false,
                }
            }

            let unshifted_page =
                match self.unshifted_vars_tparam
                    .read_path(&unshift_root, point, &mut proof)
                {
                    Some(page) => page,
                    None => return false,
                };

            let test_page = match self.fri_message_tparam[0].read_path(
                &message_roots[0],
                point / self.fri_localization,
                &mut proof,
            ) {
                Some(page) => page,
                None => return false,
            };

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
                    return false;
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
                return false;
            }
        }

        for query in 0..self.fri_checks {
            let point = hash::prf2i(final_challenge, query) & (self.evaluation_coset.size() - 1);

            let mut picked_fes = Vec::new();
            let mut picked_coords = Vec::new();

            let mut index = point;
            for message in 0..(self.fri_param.messages() - 1) {
                index /= self.fri_localization;
                let page = match self.fri_message_tparam[message].read_path(
                    &message_roots[message],
                    index,
                    &mut proof,
                ) {
                    Some(page) => page,
                    None => return false,
                };

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
                return false;
            }
        }

        return true;
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
}
