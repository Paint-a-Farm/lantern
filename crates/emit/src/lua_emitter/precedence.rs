use lantern_hir::expr::HirExpr;
use lantern_hir::types::BinOp;

/// Operator precedence levels (higher = binds tighter).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Precedence(pub(super) u8);

impl Precedence {
    pub(super) const OR: Self = Precedence(1);
    pub(super) const AND: Self = Precedence(2);
    pub(super) const COMPARE: Self = Precedence(3);
    pub(super) const CONCAT: Self = Precedence(4);
    pub(super) const ADD: Self = Precedence(5);
    pub(super) const MUL: Self = Precedence(6);
    pub(super) const UNARY: Self = Precedence(7);
    pub(super) const POW: Self = Precedence(8);

    pub(super) const POSTFIX: Self = Precedence(10);
}

pub(super) fn binop_precedence(op: BinOp) -> Precedence {
    match op {
        BinOp::Or => Precedence::OR,
        BinOp::And => Precedence::AND,
        BinOp::CompareEq
        | BinOp::CompareNe
        | BinOp::CompareLt
        | BinOp::CompareLe
        | BinOp::CompareGt
        | BinOp::CompareGe => Precedence::COMPARE,
        BinOp::Concat => Precedence::CONCAT,
        BinOp::Add | BinOp::Sub => Precedence::ADD,
        BinOp::Mul | BinOp::Div | BinOp::FloorDiv | BinOp::Mod => Precedence::MUL,
        BinOp::Pow => Precedence::POW,
    }
}

pub(super) fn expr_precedence(expr: &HirExpr) -> Precedence {
    match expr {
        HirExpr::Binary { op, .. } => binop_precedence(*op),
        HirExpr::Unary { .. } => Precedence::UNARY,
        HirExpr::Concat(_) => Precedence::CONCAT,
        _ => Precedence(20), // atoms — never need parens
    }
}

pub(super) fn binop_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::FloorDiv => "//",
        BinOp::Mod => "%",
        BinOp::Pow => "^",
        BinOp::Concat => "..",
        BinOp::CompareEq => "==",
        BinOp::CompareNe => "~=",
        BinOp::CompareLt => "<",
        BinOp::CompareLe => "<=",
        BinOp::CompareGt => ">",
        BinOp::CompareGe => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
}
