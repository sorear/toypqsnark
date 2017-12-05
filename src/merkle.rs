use field::FE;
use hash;

pub struct ParamsBuilder {
    pub num_points: usize,
    pub page_size: usize,
    pub radix: usize,
    pub expected_queries: usize,
}

impl ParamsBuilder {
    pub fn build(self) -> Params {
        let radix = self.radix;
        assert!(self.num_points.is_power_of_two());
        assert!(radix.is_power_of_two() && radix >= 2);

        let mut depth = 0;
        let mut roots = self.num_points;
        while roots >= radix && roots - (roots / radix) > (radix - 1) * self.expected_queries {
            depth += 1;
            roots /= radix;
        }

        Params {
            radix,
            depth,
            num_roots: roots,
            page_size: self.page_size,
            num_points: self.num_points,
        }
    }
}

#[derive(Clone)]
pub struct Params {
    num_points: usize,
    page_size: usize,
    radix: usize,
    depth: usize,
    num_roots: usize,
    // TODO: hash function selection
    // TODO: striding and/or hash function modifications to reduce RAM
    // TODO: allow combining pages?
}

impl Params {
    pub fn root_elements(&self) -> usize {
        self.num_roots
    }

    pub fn path_elements(&self) -> usize {
        self.depth * (self.radix - 1) + self.page_size
    }

    fn do_hash(&self, elems: &[FE]) -> FE {
        hash::hash1(elems)
    }

    pub fn read_root(&self, proof: &mut &[FE]) -> (Vec<FE>, FE) {
        let (roots, rest) = proof.split_at(self.root_elements());
        *proof = rest;

        (Vec::from(roots), self.do_hash(roots))
    }

    pub fn read_path(&self, root: &[FE], mut index: usize, proof: &mut &[FE]) -> Option<Vec<FE>> {
        assert!(index < self.num_points);
        let (page, rest) = proof.split_at(self.page_size);
        *proof = rest;

        let mut chain = self.do_hash(page);

        for _ in 0..self.depth {
            let (link, rest) = proof.split_at(self.radix - 1);
            *proof = rest;
            let mut linkv = Vec::from(link);
            linkv.push(chain);
            linkv.swap(self.radix - 1, index & (self.radix - 1));
            chain = self.do_hash(&linkv);
            index /= self.radix;
        }

        if chain == root[index] {
            Some(Vec::from(page))
        } else {
            None
        }
    }

    pub fn make_tree(&self, data: &[FE]) -> Prover {
        assert!(data.len() % self.page_size == 0);
        assert!(data.len() / self.page_size == self.num_points);

        let mut hash_levels = Vec::<Vec<FE>>::new();
        hash_levels.push(data.chunks(self.page_size).map(|c| hash::hash1(c)).collect());

        for i in 0..self.depth {
            let next = hash_levels[i-1].chunks(self.radix).map(|c| hash::hash1(c)).collect();
            hash_levels.push(next);
        }

        Prover {
            param: self.clone(),
            hash_levels,
        }
    }
}

pub struct Prover {
    param: Params,
    hash_levels: Vec<Vec<FE>>,
}

impl Prover {
    pub fn emit_path(&self, message: &[FE], mut page: usize, proof: &mut Vec<FE>) {
        let size = self.param.page_size;
        let radix = self.param.radix;
        proof.extend(&message[page * size..(page + 1) * size]);

        for l in 0..self.param.depth {
            let slot = page % radix;
            page /= radix;
            let mut level = Vec::from(&self.hash_levels[l][page * radix..(page + 1) * radix]);
            level.swap_remove(slot);
            proof.extend(&level);
        }
    }

    pub fn emit_root(&self, proof: &mut Vec<FE>) -> FE {
        proof.extend(&self.hash_levels[self.param.depth]);
        hash::hash1(&self.hash_levels[self.param.depth])
    }
}
