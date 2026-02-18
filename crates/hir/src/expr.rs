use crate::arena::ExprId;
use crate::types::{BinOp, CaptureKind, LuaValue, UnOp};
use crate::var::{RegRef, VarId};

/// A high-level expression in the HIR.
///
/// Designed from Luau's AstExpr hierarchy:
///   AstExprLocal       -> Var / Reg
///   AstExprGlobal      -> Global
///   AstExprConstant*   -> Literal
///   AstExprVarargs     -> VarArg
///   AstExprCall        -> Call
///   AstExprIndexName   -> FieldAccess
///   AstExprIndexExpr   -> IndexAccess
///   AstExprFunction    -> Closure
///   AstExprTable       -> Table
///   AstExprUnary       -> Unary
///   AstExprBinary      -> Binary
///   AstExprIfElse      -> IfExpr
///   AstExprInterpString -> InterpString
///
/// Method calls (NAMECALL) get their own variant because
/// they have distinct semantics from regular calls.
#[derive(Debug, Clone)]
pub enum HirExpr {
    /// Resolved variable reference (after constraint solving).
    Var(VarId),

    /// Unresolved register reference (before constraint solving).
    /// Carries the bytecode PC for scope lookup.
    Reg(RegRef),

    /// Literal value.
    Literal(LuaValue),

    /// Global variable access (GETGLOBAL/GETIMPORT).
    Global(String),

    /// Upvalue access (GETUPVAL).
    Upvalue(u8),

    /// Variadic arguments (...).
    VarArg,

    /// Table field access with constant string key: `expr.field`
    /// (GETTABLEKS)
    FieldAccess {
        table: ExprId,
        field: String,
    },

    /// Table index with arbitrary expression key: `expr[key]`
    /// (GETTABLE / GETTABLEN)
    IndexAccess {
        table: ExprId,
        key: ExprId,
    },

    /// Binary operation: `left op right`
    /// Includes arithmetic, comparison, concat, and/or.
    Binary {
        op: BinOp,
        left: ExprId,
        right: ExprId,
    },

    /// Unary operation: `op expr`
    Unary {
        op: UnOp,
        operand: ExprId,
    },

    /// Function call: `func(args...)`
    /// result_count: how many results are expected (0 = MULTRET)
    Call {
        func: ExprId,
        args: Vec<ExprId>,
        result_count: u8,
    },

    /// Method call: `obj:method(args...)`
    /// Compiled via NAMECALL + CALL.
    MethodCall {
        object: ExprId,
        method: String,
        args: Vec<ExprId>,
        result_count: u8,
    },

    /// Closure creation (NEWCLOSURE/DUPCLOSURE + CAPTURE).
    Closure {
        proto_id: usize,
        captures: Vec<Capture>,
    },

    /// Table constructor: `{ ... }`
    /// Array items have key=None, hash items have key=Some(expr).
    Table {
        array: Vec<ExprId>,
        hash: Vec<(ExprId, ExprId)>,
    },

    /// String concatenation: `a .. b .. c`
    /// Kept separate from Binary::Concat because CONCAT operates
    /// on a range of registers, not just two operands.
    Concat(Vec<ExprId>),

    /// If-expression: `if cond then trueExpr else falseExpr`
    /// (Luau extension, not in Lua 5.1)
    IfExpr {
        condition: ExprId,
        then_expr: ExprId,
        else_expr: ExprId,
    },

    /// Select from multi-return: takes the n-th value from a call.
    /// Used when a call returns multiple values and we need one.
    Select {
        source: ExprId,
        index: u8,
    },
}

/// A captured upvalue in a closure.
#[derive(Debug, Clone)]
pub struct Capture {
    pub kind: CaptureKind,
    pub source: CaptureSource,
}

/// Source of a captured value.
#[derive(Debug, Clone)]
pub enum CaptureSource {
    /// Capture from a local register.
    Register(RegRef),
    /// Capture from a resolved variable.
    Var(VarId),
    /// Capture from parent's upvalue slot.
    Upvalue(u8),
}
