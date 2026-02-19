mod exprs;
mod hoisting;
mod precedence;
mod stmts;

use std::fmt::Write;

use lantern_hir::func::HirFunc;
use lantern_hir::stmt::HirStmt;
use lantern_hir::var::VarId;

use rustc_hash::FxHashSet;

use crate::type_info;

/// Context for whole-file emission.
/// Maps child proto indices to their lifted HirFuncs.
pub struct FileContext<'a> {
    /// All HirFuncs in the chunk, indexed by bytecode function index.
    pub funcs: &'a [HirFunc],
    /// For each bytecode function, its child_protos table.
    /// child_protos[func_index][local_proto_id] = global bytecode func index.
    pub child_protos: &'a [Vec<usize>],
}

/// Emit a single function to Lua source text including signature.
pub fn emit_function(func: &HirFunc) -> String {
    let mut emitter = LuaEmitter::new(func, None);
    emitter.emit_with_signature();
    emitter.output
}

/// Emit a whole file: the main function's body as top-level statements,
/// with closures emitted inline and `X.Y = function(self, ...)` converted
/// to `function X:Y(...)`.
pub fn emit_file(funcs: &[HirFunc], child_protos: &[Vec<usize>], main_index: usize) -> String {
    let ctx = FileContext {
        funcs,
        child_protos,
    };

    let main_func = &funcs[main_index];
    let mut emitter = LuaEmitter::new(main_func, Some(&ctx));

    // The main function's body IS the top-level code.
    // Emit it without a function wrapper.
    if main_func.structured {
        let entry = main_func.entry;
        emitter.emit_stmts(&main_func.cfg[entry].stmts);
    }

    emitter.output
}

pub struct LuaEmitter<'a> {
    pub(crate) func: &'a HirFunc,
    pub output: String,
    pub(crate) indent: usize,
    /// Track which local variables have been declared (emitted with `local`).
    /// Pre-populated with parameters and for-loop variables.
    pub(crate) declared: FxHashSet<VarId>,
    /// File context for resolving closures to child HirFuncs.
    pub(crate) file_ctx: Option<&'a FileContext<'a>>,
}

impl<'a> LuaEmitter<'a> {
    pub fn new(func: &'a HirFunc, file_ctx: Option<&'a FileContext<'a>>) -> Self {
        // Pre-declare parameters and loop variables
        let mut declared = FxHashSet::default();
        for (var_id, info) in func.vars.iter() {
            if info.is_param || info.is_loop_var {
                declared.insert(var_id);
            }
        }

        Self {
            func,
            output: String::new(),
            indent: 0,
            declared,
            file_ctx,
        }
    }

    /// Emit the full function definition including signature and `end`.
    pub fn emit_with_signature(&mut self) {
        self.emit_signature(None);
        self.indent += 1;
        self.emit_body();
        self.indent -= 1;
        self.output.push_str("end\n");
    }

    /// Emit just the function body (no signature/end wrapper).
    pub fn emit_body(&mut self) {
        if self.func.structured {
            let entry = self.func.entry;
            let stmts = &self.func.cfg[entry].stmts;
            // Strip trailing bare return (implicit in Lua)
            let stmts = if let Some(HirStmt::Return(values)) = stmts.last() {
                if values.is_empty() { &stmts[..stmts.len() - 1] } else { stmts }
            } else {
                stmts
            };
            self.emit_stmts(stmts);
        } else {
            self.emit_unstructured();
        }
    }

    /// Emit the function signature.
    ///
    /// If `qualified_name` is provided, it overrides the function's debug name
    /// (used for `function ClassName:methodName(...)` emission).
    pub(super) fn emit_signature(&mut self, qualified_name: Option<&str>) {
        let type_info = type_info::decode_param_types(&self.func.type_info);

        // Check if first param is "self" — if so, this is a method
        let has_self = self.func.params.first().map_or(false, |p| {
            self.func.vars.get(*p).name.as_deref() == Some("self")
        });

        self.output.push_str("function");

        // Function name
        let name = qualified_name
            .map(|s| s.to_string())
            .or_else(|| self.func.name.clone());
        if let Some(name) = &name {
            self.output.push(' ');
            self.output.push_str(name);
        }

        self.output.push('(');

        // Parameters: skip "self" for method notation (it's implicit with `:`)
        let param_start = if has_self { 1 } else { 0 };
        let params = &self.func.params[param_start..];

        for (i, var_id) in params.iter().enumerate() {
            if i > 0 {
                self.output.push_str(", ");
            }

            let name = self.var_name(*var_id);
            self.output.push_str(&name);

            // Type annotation from type_info (offset by param_start since we may skip self)
            if let Some(ref ti) = type_info {
                let type_index = param_start + i;
                if let Some(type_str) = ti.param_types.get(type_index) {
                    if !type_str.is_empty() {
                        let _ = write!(self.output, ": {}", type_str);
                    }
                }
            }
        }

        if self.func.is_vararg {
            if !params.is_empty() {
                self.output.push_str(", ");
            }
            self.output.push_str("...");
        }

        self.output.push_str(")\n");
    }

    pub(crate) fn var_name(&self, var_id: VarId) -> String {
        self.func.vars.get(var_id).display_name(var_id)
    }

    pub(crate) fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
    }
}
