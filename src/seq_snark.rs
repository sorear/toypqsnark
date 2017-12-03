pub struct CSP {
    pub variables: Vec<String>,
    pub constraints: Vec<Constraint>,
}

pub struct Constraint {
    pub name: String,
    pub expr: Box<Expr>,
}

pub enum Expr {
    Const(FE),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Var(String),
    NextVar(String),
    LastFlag,
}

pub struct Assignment {
    pub values: Vec<Vec<FE>>,
}

