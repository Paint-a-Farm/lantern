/// Lua value literal — matches Luau's constant types.
#[derive(Debug, Clone, PartialEq)]
pub enum LuaValue {
    Nil,
    Boolean(bool),
    Number(f64),
    String(Vec<u8>),
    Vector(f32, f32, f32),
}

/// Binary operators — mirrors Luau's AstExprBinary::Op.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Pow,
    Concat,
    CompareNe,
    CompareEq,
    CompareLt,
    CompareLe,
    CompareGt,
    CompareGe,
    And,
    Or,
}

/// Unary operators — mirrors Luau's AstExprUnary::Op.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Minus,
    Len,
}

/// Upvalue capture type from CAPTURE instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaptureKind {
    /// Capture local by value.
    Val,
    /// Capture local by reference.
    Ref,
    /// Capture parent's upvalue.
    Upval,
}
