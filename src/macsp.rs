use field::FE;
use geom::Coset;
use std::sync::Arc;

pub struct MACSP {
    pub variables: Vec<String>,
    // the exact representation of constraints is subject to change
    pub constraints: Vec<Constraint>,
    pub coset: Coset,
}

pub struct Constraint {
    pub name: String,
    pub expr: Arc<Expr>,
}

pub enum Expr {
    Const(FE),
    Add(Arc<Expr>, Arc<Expr>),
    Mul(Arc<Expr>, Arc<Expr>),
    Var(String, FE),
}
