use crate::arena::ExprId;
use crate::types::BinOp;
use crate::var::{RegRef, VarId};

/// A high-level statement in the HIR.
///
/// Designed from Luau's AstStat hierarchy:
///   AstStatLocal          -> LocalDecl
///   AstStatAssign         -> Assign
///   AstStatCompoundAssign -> CompoundAssign
///   AstStatExpr           -> ExprStmt (call as statement)
///   AstStatReturn         -> Return
///   AstStatIf             -> If
///   AstStatWhile          -> While
///   AstStatRepeat         -> Repeat
///   AstStatFor            -> NumericFor
///   AstStatForIn          -> GenericFor
///   AstStatBreak          -> Break
///   AstStatContinue       -> Continue
///   AstStatFunction       -> FunctionDef
///   AstStatLocalFunction  -> LocalFunctionDef
#[derive(Debug, Clone)]
pub enum HirStmt {
    /// `local var [= expr]`
    LocalDecl {
        var: VarId,
        init: Option<ExprId>,
    },

    /// `local var1, var2, ... = expr1, expr2, ...`
    MultiLocalDecl {
        vars: Vec<VarId>,
        values: Vec<ExprId>,
    },

    /// `lvalue = expr`
    Assign {
        target: LValue,
        value: ExprId,
    },

    /// `lval1, lval2, ... = expr1, expr2, ...`
    MultiAssign {
        targets: Vec<LValue>,
        values: Vec<ExprId>,
    },

    /// `lvalue op= expr` (Luau compound assignment)
    CompoundAssign {
        op: BinOp,
        target: LValue,
        value: ExprId,
    },

    /// Expression used as statement (function calls).
    ExprStmt(ExprId),

    /// `return expr1, expr2, ...`
    Return(Vec<ExprId>),

    /// `if cond then body [elseif cond then body]* [else body] end`
    If {
        condition: ExprId,
        then_body: Vec<HirStmt>,
        elseif_clauses: Vec<ElseIfClause>,
        else_body: Option<Vec<HirStmt>>,
    },

    /// `while cond do body end`
    While {
        condition: ExprId,
        body: Vec<HirStmt>,
    },

    /// `repeat body until cond`
    Repeat {
        body: Vec<HirStmt>,
        condition: ExprId,
    },

    /// `for var = start, limit [, step] do body end`
    NumericFor {
        var: VarId,
        start: ExprId,
        limit: ExprId,
        step: Option<ExprId>,
        body: Vec<HirStmt>,
    },

    /// `for var1, var2, ... in iter_expr do body end`
    GenericFor {
        vars: Vec<VarId>,
        iterators: Vec<ExprId>,
        body: Vec<HirStmt>,
    },

    /// `break`
    Break,

    /// `continue`
    Continue,

    /// `function name(params) body end`
    FunctionDef {
        name: LValue,
        func_expr: ExprId,
    },

    /// `local function name(params) body end`
    LocalFunctionDef {
        var: VarId,
        func_expr: ExprId,
    },

    /// Close upvalues for registers >= target.
    /// (CLOSEUPVALS — internal, usually removed before emit)
    CloseUpvals {
        from_register: u8,
    },

    /// Pre-variable-recovery register assignment.
    /// The vars crate resolves this to Assign/LocalDecl.
    /// Internal only — removed before emit.
    RegAssign {
        target: RegRef,
        value: ExprId,
    },
}

/// An if-elseif clause.
#[derive(Debug, Clone)]
pub struct ElseIfClause {
    pub condition: ExprId,
    pub body: Vec<HirStmt>,
}

/// A location that can be assigned to.
/// Mirrors the LValue concept from Luau:
///   AstExprLocal     -> Local
///   AstExprGlobal    -> Global
///   AstExprIndexName -> Field
///   AstExprIndexExpr -> Index
#[derive(Debug, Clone)]
pub enum LValue {
    /// Local variable.
    Local(VarId),
    /// Global variable.
    Global(String),
    /// Table field: `expr.name`
    Field {
        table: ExprId,
        field: String,
    },
    /// Table index: `expr[key]`
    Index {
        table: ExprId,
        key: ExprId,
    },
    /// Upvalue.
    Upvalue(u8),
}
