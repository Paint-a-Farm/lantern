# Lantern

A Luau bytecode decompiler written in Rust, designed for Farming Simulator 25 script analysis. Produces readable Lua source from compiled `.l64` bytecode files.

Lantern is a ground-up rewrite that replaces [medal](https://github.com/scfmod/medal)'s SSA-based pipeline with constraint-based variable recovery and compiler-aware pattern matching. The result is a simpler architecture that avoids entire classes of decompilation bugs at their source rather than fighting them with heuristics.

## Quick Start

```bash
# Build
cargo build

# Decompile a single file
lantern --file script.l64

# Decompile an entire directory
lantern --file --output-dir ./output/ /path/to/scripts/

# Inspect a specific function
lantern --emit 6 script.l64

# Dump raw bytecode disassembly
lantern --dump script.l64
```

## Architecture

```
.l64 file ─► Parse ─► Lift ─► Variable Recovery ─► Expression Optimization
                                                            │
Lua source ◄─ Format ◄─ Emit ◄─ Patterns ◄─ Structure ◄───┘
```

Lantern processes bytecode through eleven crates, each handling a distinct phase:

| Crate       | Purpose                                                                         |
| ----------- | ------------------------------------------------------------------------------- |
| `bytecode`  | Parse encrypted `.l64` files into instructions, constants, and debug info       |
| `hir`       | Core intermediate representation — flat expression arena, variable table, CFG   |
| `lift`      | Translate bytecode opcodes to HIR; detect boolean value computation patterns    |
| `vars`      | Constraint-based variable recovery using debug scopes as hard boundaries        |
| `exprs`     | Split multi-def temps, eliminate temporaries, fold tables, inline branch-locals |
| `structure` | Collapse flat CFG into nested if/while/for/repeat control flow                  |
| `patterns`  | Post-structuring transforms: compound conditions, guard clauses, elseif chains  |
| `emit`      | Recursive descent Lua source generation with operator precedence                |
| `lantern`   | Library crate — wires the full pipeline together for embedding in other tools   |
| `verify`    | Roundtrip verification: decompile → recompile → bytecode comparison             |
| `cli`       | Command-line interface, batch processing, timing                                |

### Key Design Decisions

**Expression arena instead of nested trees.** All expressions live in a flat `Vec<HirExpr>` indexed by `ExprId` (u32). Substituting an expression during temp elimination is O(1) — just overwrite the slot. Medal uses nested `Box<RValue>` trees where substitution requires cloning entire subtrees.

**Constraint-based variable recovery instead of SSA.** Medal's SSA construction assigns variable identity in a single DFS pass. Once it decides two register accesses belong to the same variable, nothing downstream can correct it. Lantern collects constraints from _all_ instructions and debug scopes simultaneously, then solves with union-find. Debug scopes are hard separation boundaries — two accesses to the same register in different scopes are guaranteed to produce different variables.

**Compiler-aware boolean pattern detection.** Before CFG construction, lantern pre-scans for bytecode patterns the Luau compiler generates for boolean expressions used as values (`a and b or c`, comparison chains, `x == Y or x == Z`). These patterns' internal jumps are suppressed from block boundary creation, preventing false CFG fragmentation that would produce broken control flow.

**No Arc/Mutex anywhere.** Variables are `VarId` (u32), expressions are `ExprId` (u32). No interior mutability, no reference counting, no borrow checker fights.

## Pipeline Details

### 1. Bytecode Parsing

Parses Luau bytecode version 6 (all FS25 scripts). Handles XOR encryption with encode key 1. Extracts:

- 83 opcodes (NOP through IDIVK) in ABC/AD/E instruction formats
- Constants: nil, boolean, number, string, import, table, closure, vector
- Debug info: function names, register scope ranges, line mappings, type annotations
- Scope tree: interval-based register-to-name lookup (replaces medal's scope extension hack)

### 2. Lifting

Each opcode maps to HIR expressions and statements. Block discovery identifies basic block boundaries from jumps, branches, for-loop instructions, and returns. Boolean region detection identifies four patterns:

- **Bool regions**: `LOADB Rx, false, +1` / `LOADB Rx, true` pairs — comparison-as-value
- **And/or ternaries**: `JumpIfNot Ra → fallback; [compute b]; JumpIf Rb → join; [c]` — `a and b or c`
- **Value ternaries**: `JumpIfNot → false_val; [true_val]; Jump → join; [false_val]` — conditional assignment
- **Truthy chains**: `JumpIf` cascades — `a or b or c` value chains

All support compound conditions (multiple conditional jumps targeting the same fallback) and comparison-based conditions (JumpIfEq, JumpXEqKN, etc.).

### 3. Variable Recovery

The constraint solver replaces medal's entire SSA pipeline:

1. **Constraint generation**: Scan all instructions for register defs/uses. Extract debug scope info (name + PC range). Mark overlapping-scope accesses as MustAlias, different-scope accesses as MustNotAlias.
2. **Scope-based binding**: Parameters bound first. Then scoped accesses matched by strict PC containment. Pre-scope initializer patterns recognized (compiler writes at scope_start - 1).
3. **Reaching-def analysis**: Unscoped uses resolved through CFG predecessor analysis.
4. **Rewrite**: All raw register references replaced with resolved VarIds.

This eliminates the "kioskMode bug" — where medal's SSA incorrectly merges a number and an object stored in the same register across different scopes — at the source.

### 4. Expression Optimization

Five passes, run twice (before and after structuring):

- **Multi-def temp splitting**: The Luau compiler reuses registers for sequential temporaries, causing the var solver to merge them into one multi-def VarId. This pass splits each def into a fresh single-def variable, making them eligible for inlining.
- **Temporary elimination**: Single-def, single-use, unnamed variables → inline the expression. O(1) arena substitution.
- **Multi-return collapse**: `local _v1, _v2 = call(); x = _v1; y = _v2` → `x, y = call()`
- **Table constructor folding**: `local t = {}; t[1] = x; t.name = y` → `local t = {x, name = y}`
- **Branch-local inlining**: Temps scoped to if/else branches inlined independently per branch, even when the same VarId appears in multiple branches.

### 5. CFG Structuring

Iterative region analysis inspired by [SAILR (USENIX Security 2024)](https://www.usenix.org/conference/usenixsecurity24/presentation/basque):

- **While loops**: Back-edge detection, condition extraction, break/continue through loop context
- **Numeric for**: FORNPREP/FORNLOOP opcode pairs
- **Generic for**: FORGPREP/FORGLOOP with iterator variable extraction
- **If/else**: Branch terminator analysis with recursive arm structuring
- **Guards**: Early-exit patterns (`if cond then break/return end`) preserved as guards

### 6. Post-Structuring Patterns

Applied on the nested statement tree:

- **Compound conditions**: `if A then if B then body end end` → `if A and B then body end`
- **Elseif normalization**: Nested else-if chains flattened
- **Guard flipping**: Single guards converted to wrapping if blocks when cleaner
- **Return temp inlining**: `local v = expr; return v` → `return expr`
- **Boolean value recovery**: `r = true; if cond then else r = false end` → `r = cond`

### 7. Emission

Recursive descent over structured HIR. Handles:

- Method detection (first param = "self" → colon syntax)
- Operator precedence and minimal parenthesization
- Upvalue hoisting (declares captured locals in outer scope)
- IIFE wrapping for immediately-invoked closures
- Expression statement decomposition (`cond and call()` → `if cond then call() end`)
- Type annotations from bytecode (Luau-specific)
- Output formatted by [stylua](https://github.com/JohnnyMorganz/StyLua) with Luau syntax

## Comparison with Medal

Both lantern and medal target Luau bytecode decompilation. Medal is a mature, general-purpose decompiler supporting Luau versions 3-6 and Lua 5.1. Lantern is specialized for FS25 (version 6 only) with a focus on output quality.

### Architectural Differences

|                        | Medal                     | Lantern                                 |
| ---------------------- | ------------------------- | --------------------------------------- |
| **Variable identity**  | SSA (one-pass DFS)        | Constraint solver (all-at-once)         |
| **Expression storage** | Nested `Box<RValue>`      | Flat arena (`Vec<HirExpr>`)             |
| **Variable handle**    | `Arc<Mutex<RcLocal>>`     | `VarId` (u32)                           |
| **CFG edges**          | `Vec<(RcLocal, RValue)>`  | `Vec<(VarId, ExprId)>`                  |
| **Boolean patterns**   | Inline during structuring | Pre-scan before CFG construction        |
| **Temp elimination**   | ~800 lines of heuristics  | Simple criteria (1 def, 1 use, no name) |
| **Rust toolchain**     | Nightly (required)        | Stable                                  |
| **Bytecode versions**  | 3, 4, 5, 6                | 6 only                                  |
| **Codebase size**      | ~15k lines, 7 crates      | ~25k lines, 11 crates                   |

### What Medal Does Better

- **Broader version support**: Medal handles Luau versions 3-6 and has a Lua 5.1 backend. Lantern only supports version 6.
- **Web interface**: Medal includes a Cloudflare Workers crate for browser-based decompilation.
- **Multi-return scoping**: Medal correctly scopes `local r, g, b, a` declarations inside branches where they're used. Lantern sometimes hoists these to function scope.

### What Lantern Does Better

- **No identity bugs**: The constraint solver respects debug scope boundaries as hard constraints. Register reuse across scopes (the "kioskMode bug") is impossible by construction.
- **Fewer unnamed temporaries**: Multi-def splitting, branch-local inlining, and multi-return collapse eliminate temps that medal's global use-count analysis misses. Across the full FS25 corpus: 6 remaining `local _v = nil` declarations and ~330 total unnamed temp variables.
- **Syntactically valid output**: 0 SyntaxErrors across all FS25 scripts. Medal produces a handful of syntax issues in complex files.
- **Simpler internals**: No Arc/Mutex, no nightly Rust, no SSA construction/destruction phases. Easier to understand and extend despite the larger codebase.
- **Faster builds**: Stable Rust, fewer dependencies, no nightly feature gates. Debug builds complete in <1 second incremental.

### Output Comparison

Both decompilers produce near-identical output for straightforward code. Differences emerge in complex functions with register reuse across scopes.

**Register reuse — lantern wins on correctness:**

```lua
-- Lantern: correctly separates variables
local kioskMode = g_gameSettings:getValue(GameSettings.SETTING.KIOSK_MODE)
-- ... later, different scope ...
local farmId = g_farmManager:getFarmByUserId(userId)

-- Medal: incorrectly merges into one variable
local kioskMode = g_gameSettings:getValue(GameSettings.SETTING.KIOSK_MODE)
-- ... later ...
kioskMode = g_farmManager:getFarmByUserId(userId)  -- wrong!
```

**Temp elimination — lantern wins on readability:**

```lua
-- Lantern: inlines sequential temporaries
if not hasXMLProperty(xmlFile, key) then break end

-- Medal: preserves compiler temporaries
local _v8 = hasXMLProperty(xmlFile, key)
if not _v8 then break end
```

## CLI Reference

```
lantern [OPTIONS] <FILE>...

Arguments:
  <FILE>...     Input .l64 file(s)

Options:
  --file            Full-file mode (emit as .lua with top-level code)
  --emit <N>        Emit only function index N
  --dump            Bytecode disassembly mode
  --raw             Skip variable recovery and structuring
  --no-format       Skip stylua formatting
  --output-dir <D>  Write .lua files to directory (preserves structure)
  -h, --help        Print help
```

### Examples

```bash
# Decompile a single script
lantern --file PlayerManager.l64 > PlayerManager.lua

# Batch decompile with directory structure
lantern --file --output-dir ./decompiled/ /path/to/scripts/**/*.l64

# Inspect function #12 with timing info
lantern --emit 12 EconomyManager.l64

# Debug: see raw bytecode
lantern --dump SomeScript.l64

# Debug: see HIR before structuring
lantern --raw --emit 0 SomeScript.l64

# Roundtrip verification (single file)
cargo run -p lantern-verify -- roundtrip script.l64

# Roundtrip verification (entire corpus)
cargo run -p lantern-verify -- roundtrip /path/to/scripts/
```

## Building

Requires stable Rust (no nightly needed):

```bash
cargo build        # debug build (fast, recommended for development)
cargo build --release  # optimized build
```

## Project Status

Lantern successfully decompiles all 30,315 functions across the FS25 base game. Output quality metrics:

- **Syntax errors** (via luau-analyze): 0
- **Roundtrip match rate**: 93.1% (decompile → recompile produces identical bytecode)
- **Nil-initialized temps** (`local _v = nil`): 6
- **Total unnamed temp declarations**: ~330
- **Empty if-then-end blocks**: 0

Areas of active development:

- Inlined function reconstruction (Luau compiler inlines small local functions)
- For-loop bound variable scoping

## License

MIT
