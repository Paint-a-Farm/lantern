use std::fs;
use std::path::PathBuf;
use std::process::Command;

use anyhow::{bail, Context, Result};
use clap::Args;

use crate::analyze;

/// Grammar-backed and compiler-sensitive Luau snippets.
///
/// Source grammar reference:
/// https://luau.org/grammar/
#[derive(Debug, Clone, Copy)]
pub struct GrammarCase {
    pub id: &'static str,
    pub description: &'static str,
    pub source: &'static str,
}

#[derive(Debug, Args)]
pub struct GrammarCasesArgs {
    /// Directory to write `.luau` case files.
    #[arg(long, default_value = "crates/verify/corpus/grammar")]
    pub out_dir: PathBuf,

    /// Skip luau-analyze pass after writing cases.
    #[arg(long)]
    pub skip_analyze: bool,

    /// Skip luau-compile parse/bytecode pass after writing cases.
    #[arg(long)]
    pub skip_compile: bool,
}

pub fn run_grammar_cases(args: GrammarCasesArgs) -> Result<()> {
    let cases = grammar_cases();
    fs::create_dir_all(&args.out_dir).with_context(|| {
        format!(
            "failed to create case output directory {}",
            args.out_dir.display()
        )
    })?;

    let mut paths = Vec::with_capacity(cases.len());
    for case in cases {
        let filename = format!("{}.luau", case.id);
        let path = args.out_dir.join(filename);
        let mut content = String::new();
        content.push_str("-- ");
        content.push_str(case.description);
        content.push('\n');
        content.push_str(case.source);
        content.push('\n');
        fs::write(&path, content).with_context(|| format!("failed to write {}", path.display()))?;
        paths.push(path);
    }

    println!(
        "wrote {} grammar cases to {}",
        paths.len(),
        args.out_dir.display()
    );

    if !args.skip_analyze {
        let report = analyze::run_luau_analyze(&paths)?;
        println!(
            "luau-analyze: {} diagnostics ({} syntax errors)",
            report.total_diagnostics(),
            report.syntax_errors
        );
        for line in report.samples.iter().take(10) {
            println!("  {}", line);
        }
        if report.syntax_errors > 0 {
            bail!(
                "grammar case corpus has {} syntax errors",
                report.syntax_errors
            );
        }
    }

    if !args.skip_compile {
        let mut compile_failures = Vec::new();
        for path in &paths {
            let output = Command::new("luau-compile")
                .arg("--binary")
                .arg(path)
                .output()
                .with_context(|| {
                    format!("failed to execute luau-compile for {}", path.display())
                })?;
            if !output.status.success() {
                compile_failures.push(format!(
                    "{}: {}",
                    path.display(),
                    String::from_utf8_lossy(&output.stderr).trim()
                ));
            }
        }

        if compile_failures.is_empty() {
            println!("luau-compile: all cases compiled successfully");
        } else {
            for line in compile_failures.iter().take(10) {
                println!("  {}", line);
            }
            bail!(
                "luau-compile failed for {} grammar cases",
                compile_failures.len()
            );
        }
    }

    Ok(())
}

pub fn grammar_cases() -> &'static [GrammarCase] {
    &[
        GrammarCase {
            id: "001_assignments",
            description: "Assignment statement forms and table lvalues",
            source: r#"local a, b = 1, 2
a, b = b, a
local t = {}
t.x = a + b
t[a] = b
return t.x, t[a]"#,
        },
        GrammarCase {
            id: "002_compound_assign",
            description: "Compound assignment operators",
            source: r#"local x = 10
x += 1
x -= 2
x *= 3
x //= 2
x %= 5
return x"#,
        },
        GrammarCase {
            id: "003_do_block",
            description: "do-end block and block-local binding",
            source: r#"local x = 1
do
    local y = 2
    x = x + y
end
return x"#,
        },
        GrammarCase {
            id: "004_while_break_continue",
            description: "while loop with continue and break",
            source: r#"local i = 0
local sum = 0
while i < 10 do
    i += 1
    if i % 2 == 0 then
        continue
    end
    if i > 7 then
        break
    end
    sum += i
end
return sum"#,
        },
        GrammarCase {
            id: "005_repeat_until",
            description: "repeat-until loop with mutation",
            source: r#"local n = 0
repeat
    n += 1
until n >= 3
return n"#,
        },
        GrammarCase {
            id: "006_if_elseif_else",
            description: "if/elseif/else statement chains",
            source: r#"local function classify(v)
    if v < 0 then
        return "neg"
    elseif v == 0 then
        return "zero"
    else
        return "pos"
    end
end

return classify(-1), classify(0), classify(2)"#,
        },
        GrammarCase {
            id: "007_numeric_for",
            description: "numeric for-loop with explicit step",
            source: r#"local total = 0
for i = 1, 9, 2 do
    total += i
end
return total"#,
        },
        GrammarCase {
            id: "008_generic_for",
            description: "generic for-loop over custom iterator",
            source: r#"local function iterFactory(values)
    local i = 0
    return function()
        i += 1
        if i <= #values then
            return i, values[i]
        end
        return nil
    end
end

local sum = 0
for _, v in iterFactory({1, 2, 3, 4}) do
    sum += v
end
return sum"#,
        },
        GrammarCase {
            id: "009_local_function",
            description: "local recursive function declaration",
            source: r#"local function fact(n)
    if n <= 1 then
        return 1
    end
    return n * fact(n - 1)
end

return fact(5)"#,
        },
        GrammarCase {
            id: "010_method_def_colon",
            description: "method syntax and colon calls",
            source: r#"local Obj = {}
Obj.__index = Obj

function Obj:new(v)
    return setmetatable({v = v}, Obj)
end

function Obj:add(delta)
    self.v += delta
    return self.v
end

local o = Obj:new(10)
return o:add(5)"#,
        },
        GrammarCase {
            id: "011_if_expression",
            description: "Luau if-expression in expression position",
            source: r#"local x = 5
local y = if x > 3 then x else 0
return y"#,
        },
        GrammarCase {
            id: "012_vararg_multiret",
            description: "varargs and multi-return assignment",
            source: r#"local function split(...)
    local a, b, c = ...
    return a, b, c
end

local x, y, z = split(1, 2, 3)
return x + y + z"#,
        },
        GrammarCase {
            id: "013_table_constructor",
            description: "table constructor forms: array/hash/index keys",
            source: r#"local k = "name"
local t = {
    1,
    2,
    [10] = 20,
    [k] = "lantern",
    flag = true,
}
return t[1], t[10], t[k], t.flag"#,
        },
        GrammarCase {
            id: "014_function_call_forms",
            description: "call argument grammar: (), string, table literal",
            source: r#"local function f(...)
    return ...
end

local a = f(1, 2, 3)
local b = f"hello"
local c = f{value = 7}
return a, b, c.value"#,
        },
        GrammarCase {
            id: "015_unary_binary_precedence",
            description: "unary/binary operator precedence and associativity",
            source: r#"local x = -3 + 10 / 2 ^ 2 .. ""
local y = not false and (1 < 2 or 3 < 2)
return x, y"#,
        },
        GrammarCase {
            id: "016_type_alias_union_intersection",
            description: "type aliases with union/intersection table types",
            source: r#"type Point = { x: number, y: number }
type Named = { name: string }
type NamedPoint = Point & Named

local p: NamedPoint = { x = 1, y = 2, name = "pt" }
return p.x + p.y"#,
        },
        GrammarCase {
            id: "017_generic_function",
            description: "generic function declaration and explicit type args",
            source: r#"local function id<T>(x: T): T
    return x
end

local n: number = id(5)
return n"#,
        },
        GrammarCase {
            id: "018_function_type_annotation",
            description: "function type annotation and typed anonymous function",
            source: r#"type Mapper = (number) -> number

local function apply(f: Mapper, x: number): number
    return f(x)
end

return apply(function(v: number): number
    return v * 2
end, 21)"#,
        },
        GrammarCase {
            id: "019_type_cast",
            description: "as-expression style type cast (::)",
            source: r#"local x = (1 :: number) + 2
return x"#,
        },
        GrammarCase {
            id: "020_string_interpolation",
            description: "interpolated string literal",
            source: r#"local name = "world"
local msg = `hello {name}`
return msg"#,
        },
        GrammarCase {
            id: "021_table_indexer_type",
            description: "table indexer type syntax",
            source: r#"type Dict = { [string]: number }
local d: Dict = { a = 1, b = 2 }
d["c"] = 3
return d.a + d.b + d.c"#,
        },
        GrammarCase {
            id: "022_export_type_alias",
            description: "exported generic type alias syntax",
            source: r#"export type Pair<T> = { first: T, second: T }
local p: Pair<number> = { first = 1, second = 2 }
return p.first + p.second"#,
        },
        GrammarCase {
            id: "023_typeof_type",
            description: "typeof type syntax",
            source: r#"local v = { x = 1 }
type V = typeof(v)
local c: V = { x = 2 }
return c.x"#,
        },
        GrammarCase {
            id: "024_nested_closure_capture",
            description: "nested closure captures and mutation",
            source: r#"local function makeCounter()
    local n = 0
    return function()
        n += 1
        return n
    end
end

local c = makeCounter()
return c(), c(), c()"#,
        },
        GrammarCase {
            id: "025_short_circuit_value",
            description: "short-circuit boolean value pattern (a and b or c)",
            source: r#"local calls = 0
local function touch(v)
    calls += 1
    return v
end

local x = touch(false) and touch(1) or touch(2)
return x, calls"#,
        },
        GrammarCase {
            id: "026_return_path_integrity",
            description: "explicit return path integrity in branches",
            source: r#"local function absLike(x: number): number
    if x >= 0 then
        return x
    end
    return -x
end

return absLike(-4), absLike(7)"#,
        },
        GrammarCase {
            id: "027_multi_return_flow",
            description: "multi-return propagation through caller",
            source: r#"local function pair(v)
    return v, v + 1
end

local function consume()
    local a, b = pair(10)
    return a * b
end

return consume()"#,
        },
        GrammarCase {
            id: "028_repeat_continue_emulation",
            description: "repeat-until with branch-heavy control flow",
            source: r#"local i = 0
local acc = 0
repeat
    i += 1
    if i % 2 == 1 then
        acc += i
    end
until i >= 7
return acc"#,
        },
    ]
}
