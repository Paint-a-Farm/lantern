# Lantern Implementation Plan

## Context

The existing "medal" decompiler follows a classical one-directional pipeline (Bytecode -> CFG -> SSA -> Structuring -> AST -> Output) where errors compound through stages. The root architectural problem: SSA construction makes irreversible identity decisions based on incomplete information, and every downstream stage fights those decisions with heuristics. The kioskMode bug is a perfect example -- register R5 is reused for a number and an object, SSA assigns the wrong identity to nested reads, and 700+ lines of inline heuristics can't fix it.

A ground-up rewrite using modern techniques (constraint-based variable recovery, compiler-aware pattern matching, arena-based IR) eliminates these problems at their source rather than patching them downstream.

### Key Research Insights Applied

- **SAILR (USENIX 2024)**: Compiler-aware structuring beats generic algorithms. Since we know the exact Luau compiler, we can match its output patterns precisely.
- **Constraint-based variable recovery**: Replace SSA's "assign identity once" with a union-find solver that processes ALL register uses simultaneously, using debug scopes as hard separation boundaries.
- **Arena-based IR**: Flat expression arena with `ExprId` indices instead of medal's nested `Box<RValue>` trees. O(1) substitution, no borrow checker fights.
- **Luau bytecode debug info**: Registers have name+scope ranges (`[start_pc, end_pc)`). These are hard constraints on variable identity, not soft hints with extension hacks.
- **Target version 6 only**: All FS25 scripts are bytecode version 6. This guarantees type annotations are available.

---

## Architecture Overview

```
Bytecode --> Parse --> Lift --> Pattern Match --> Structure --> Emit
               |         |          |                  |           |
             BcFunc    HirFunc    HirFunc           HirFunc    Lua source
              +debug     +CFG      +vars              +structured
              +types     +exprs    +temps eliminated   control flow
                           |
                     Constraint Solver
                     (variable recovery)
```

**The critical difference from medal**: Phases 2-4 form an **iterative fixpoint loop**. Pattern matching informs constraints, constraints inform structuring, structuring reveals new patterns. Medal's pipeline is one-directional -- once SSA assigns an identity, nothing can correct it.

---

## Crate Structure

```
lantern/
  crates/
    bytecode/       # Parsing: binary -> BcFunc (port from medal's deserializer)
    hir/            # Core IR: ExprArena, HirFunc, VarId, VarTable
    lift/           # Bytecode -> HIR with CFG (port from medal's lifter)
    vars/           # Constraint-based variable recovery (REPLACES SSA)
    patterns/       # Compiler-aware Luau pattern library
    structure/      # CFG -> structured control flow (SAILR-inspired)
    exprs/          # Temporary elimination via arena substitution
    emit/           # HIR -> Lua source text
    cli/            # Binary entry point
```

### Key Dependencies

| Crate | Purpose |
|-------|---------|
| `nom` | Binary bytecode parsing |
| `petgraph` | CFG graph representation and algorithms |
| `rustc-hash` | Fast hash maps (FxHashMap) |
| `clap` | CLI argument parsing |
| `anyhow` | Error handling |

---

## Component Details

### 1. Bytecode Parsing (`bytecode` crate) - DONE

Ported from medal's nom-based parser with debug info as first-class:

- `Chunk`: string table, function prototypes, main index
- `Function`: instructions, constants, child protos, debug info
- `Instruction`: unified struct (op, a, b, c, d, e, aux)
- `Opcode`: all 83 Luau opcodes (NOP through IDIVK)
- `Constant`: Nil, Boolean, Number, String, Import, Table, Closure, Vector
- `ScopeTree`: interval-based register-to-name lookup (replaces medal's SCOPE_EXTENSION hack)
- `LineInfo`: PC-to-source-line mapping
- `DebugInfo`: function name, scopes, upvalue names, line info

Tested: successfully parses all ~48 .l64 files in dataS/scripts/.

### 2. High-Level IR (`hir` crate)

**Replaces**: medal's separate `ast::RValue`/`RcLocal`/`Block` types

The core innovation: an **expression arena** with flat `ExprId` references.

```rust
pub type VarId = u32;   // opaque handle into VarTable
pub type ExprId = u32;  // opaque handle into ExprArena

pub struct HirFunc {
    pub cfg: StableDiGraph<HirBlock, HirEdge>,
    pub entry: NodeIndex,
    pub exprs: ExprArena,     // ALL expressions stored flat
    pub vars: VarTable,       // ALL variables with metadata
    pub origins: OriginMap,   // every HIR element -> bytecode PC
}

pub struct ExprArena { exprs: Vec<HirExpr> }

pub enum HirExpr {
    Var(VarId),
    Literal(LuaValue),
    Global(String),
    Index { table: ExprId, key: ExprId },
    Binary { op: BinOp, left: ExprId, right: ExprId },
    Unary { op: UnOp, operand: ExprId },
    Call { func: ExprId, args: Vec<ExprId> },
    MethodCall { obj: ExprId, method: String, args: Vec<ExprId> },
    Closure { proto_id: usize, upvalues: Vec<Upvalue> },
    Table { array: Vec<ExprId>, hash: Vec<(ExprId, ExprId)> },
    VarArg,
}
```

**Why this fixes medal's problems**:
- Medal's `RcLocal` is `Arc<Mutex<Local>>` -- pointer identity for equality, interior mutability everywhere, borrow checker fights. Lantern uses plain `VarId` (u32).
- Medal's `RValue` is deeply nested with `Box<>`. Substituting an expression requires cloning the entire tree. Lantern's arena substitution is O(1).
- Medal's CFG edges carry `Vec<(RcLocal, RValue)>` for phi arguments. Lantern's edges carry `Vec<(VarId, ExprId)>`.

### 3. Bytecode -> HIR Lifting (`lift` crate)

**Port from**: medal's lifter

Port medal's block discovery and instruction lifting, but output HIR instead of CFG+SSA.

Key changes:
- **No SSA construction.** Lifting produces raw `Register(u8)` references in expressions. These are resolved later by the constraint solver.
- **Debug info attached during lifting.** Each `Register(u8)` reference carries its bytecode PC, enabling the constraint solver to look up the correct scope.
- **For-loop detection during lifting.** FORNPREP/FORNLOOP and FORGPREP/FORGLOOP are recognized here (they're unambiguous bytecode patterns).

### 4. Constraint-Based Variable Recovery (`vars` crate)

**Replaces**: medal's entire SSA pipeline

This is the **core architectural change**. Instead of SSA's "assign identity in one DFS pass", generate constraints from ALL instructions, then solve simultaneously.

```rust
pub enum Constraint {
    MustAlias(RegAccess, RegAccess),      // same variable
    MustNotAlias(RegAccess, RegAccess),   // different variables
    HasName(RegAccess, String),           // from debug info
    HasType(RegAccess, LuaType),          // from type annotations
    Def(u8, usize),                       // register written at PC
    Use(u8, usize),                       // register read at PC
}
```

**Constraint generation**:
1. **From instructions**: Each write -> Def(reg, pc). Each read -> Use(reg, pc). MOVE instructions -> MustAlias if scopes overlap.
2. **From debug info** (hard constraints): Two accesses to the same register in **different** scopes get MustNotAlias.
3. **From control flow**: Reaching definitions analysis. A def that reaches a use through the CFG -> MustAlias.
4. **From type info**: Bytecode type annotations -> HasType constraints.

**Solving**: Union-find with weighted quick union.

**Why this fixes the kioskMode bug**: Debug info shows R5@number and R5@object are in different scopes. MustNotAlias prevents merging. Problem eliminated at the source.

### 5. Compiler-Aware Pattern Matching (`patterns` crate)

Since the Luau compiler is deterministic, specific bytecode patterns map 1:1 to source constructs:

- 100% confidence: NumericFor, GenericFor, NAMECALL, FASTCALL, SETLIST
- High confidence: and/or chains, ternary expressions
- Medium confidence: while loops, repeat-until, if-then-else

Applied before variable recovery -- reducing the CFG before constraint solving means fewer variables.

### 6. CFG Structuring (`structure` crate)

SAILR-inspired: after pattern matching handles the certain cases, remaining CFG goes through iterative structural analysis:

1. Apply certain patterns (for loops already in HIR)
2. Iterative: collapse linear sequences, structure if/while/repeat, merge short-circuits
3. Irreducible cases -> goto (should be very rare)

### 7. Expression Recovery (`exprs` crate)

Temporary elimination becomes trivial with correct variable identities:
- Single def, single use, no debug name -> temporary
- O(1) arena substitution
- No heuristics needed (the hard work was done by the constraint solver)

### 8. Lua Emitter (`emit` crate)

Straightforward recursive descent over structured HIR -> Lua source text.

---

## What We Reuse from Medal

| Component | Reuse Strategy |
|-----------|---------------|
| Bytecode parser | Ported to new types, kept nom parsing logic |
| Opcode enum | Ported directly |
| Instruction semantics | Port lifting logic to HIR |
| Block discovery | Port CFG construction |
| Formatter | Port emission logic |
| Boolean simplification | Port expression simplification rules |

| Component | Replaced By |
|-----------|-------------|
| SSA construction | Constraint solver |
| SSA destruction | Not needed (no SSA) |
| SSA inline | Not needed |
| Restructurer | Pattern matcher + SAILR structurer |
| Inline temporaries | Arena-based elimination |
| Name locals | Constraint solver handles naming |

---

## Implementation Phases

### Phase A: Foundation
1. [x] Set up workspace structure
2. [x] Port `bytecode` crate with ScopeTree
3. [ ] Build `hir` crate: ExprArena, HirFunc, VarId, VarTable
4. [ ] Build `lift` crate: block discovery + instruction lifting to HIR

**Milestone**: Can parse any FS25 .l64 file and produce an unstructured HIR with CFG.

### Phase B: Variable Recovery
5. [ ] Build `vars` crate: constraint generation from instructions + debug info
6. [ ] Implement union-find solver
7. [ ] Integrate with HIR: resolve Register(u8) -> VarId throughout

**Milestone**: All variables correctly identified. The kioskMode register-reuse case produces two separate VarIds.

### Phase C: Structuring & Expression Recovery
8. [ ] Build `patterns` crate: for-loops, NAMECALL, boolean chains
9. [ ] Build `structure` crate: if/while/repeat recovery
10. [ ] Build `exprs` crate: temporary elimination

**Milestone**: Structured HIR with temporaries eliminated.

### Phase D: Output & Polish
11. [ ] Build `emit` crate: Lua source generation
12. [ ] Build `cli` crate: full command-line interface
13. [ ] Iterative fixpoint loop between phases
14. [ ] Differential testing against medal output on entire dataS corpus

**Milestone**: End-to-end decompilation of all FS25 scripts, with fewer unnamed temporaries and no identity bugs compared to medal.

---

## Verification

1. **Unit tests per crate**: Each crate has tests against small bytecode snippets with known output
2. **Differential testing**: Decompile all ~48 files in dataS/scripts/ with both medal and lantern, compare:
   - Fewer unnamed temporaries (lantern should be strictly better)
   - No identity bugs (kioskMode case, mods.lua naming issues)
   - Correct control flow (for loops, if/else, while)
3. **Roundtrip testing**: For scripts where we have original source, compare decompiled output structurally
4. **Regression suite**: Known problematic files (main.lua kioskMode, mods.lua naming) as explicit test cases
