use lantern_bytecode::chunk::Chunk;
use lantern_bytecode::constant::Constant;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareMode {
    Loose,
    Strict,
}

pub fn chunks_equivalent(a: &Chunk, b: &Chunk, mode: CompareMode) -> Result<(), String> {
    if a.functions.len() != b.functions.len() {
        return Err(format!(
            "function count mismatch: {} vs {}",
            a.functions.len(),
            b.functions.len()
        ));
    }
    if a.main != b.main {
        return Err(format!("main function mismatch: {} vs {}", a.main, b.main));
    }

    for (idx, (fa, fb)) in a.functions.iter().zip(b.functions.iter()).enumerate() {
        if fa.num_params != fb.num_params {
            return Err(format!(
                "fn#{idx} num_params mismatch: {} vs {}",
                fa.num_params, fb.num_params
            ));
        }
        if fa.is_vararg != fb.is_vararg {
            return Err(format!("fn#{idx} vararg mismatch"));
        }
        if fa.num_upvalues != fb.num_upvalues {
            return Err(format!(
                "fn#{idx} upvalue count mismatch: {} vs {}",
                fa.num_upvalues, fb.num_upvalues
            ));
        }

        let a_hist = opcode_histogram(fa);
        let b_hist = opcode_histogram(fb);
        if a_hist != b_hist {
            return Err(format!("fn#{idx} opcode histogram mismatch"));
        }

        let a_consts = constant_histogram(fa.constants.as_slice());
        let b_consts = constant_histogram(fb.constants.as_slice());
        if a_consts != b_consts {
            return Err(format!("fn#{idx} constant histogram mismatch"));
        }

        if mode == CompareMode::Strict {
            if fa.instructions.len() != fb.instructions.len() {
                return Err(format!(
                    "fn#{idx} instruction count mismatch: {} vs {}",
                    fa.instructions.len(),
                    fb.instructions.len()
                ));
            }
            if fa.child_protos.len() != fb.child_protos.len() {
                return Err(format!(
                    "fn#{idx} child proto count mismatch: {} vs {}",
                    fa.child_protos.len(),
                    fb.child_protos.len()
                ));
            }

            for (pc, (ia, ib)) in fa
                .instructions
                .iter()
                .zip(fb.instructions.iter())
                .enumerate()
            {
                if ia.op != ib.op {
                    return Err(format!(
                        "fn#{idx} opcode mismatch at pc {pc}: {:?} vs {:?}",
                        ia.op, ib.op
                    ));
                }
            }
        }
    }

    Ok(())
}

fn opcode_histogram(func: &lantern_bytecode::function::Function) -> [u32; 83] {
    let mut hist = [0_u32; 83];
    for insn in &func.instructions {
        let idx = insn.op as usize;
        if idx < hist.len() {
            hist[idx] += 1;
        }
    }
    hist
}

fn constant_histogram(constants: &[Constant]) -> [u32; 8] {
    let mut hist = [0_u32; 8];
    for constant in constants {
        let idx = match constant {
            Constant::Nil => 0,
            Constant::Boolean(_) => 1,
            Constant::Number(_) => 2,
            Constant::String(_) => 3,
            Constant::Import(_) => 4,
            Constant::Table(_) => 5,
            Constant::Closure(_) => 6,
            Constant::Vector(_, _, _, _) => 7,
        };
        hist[idx] += 1;
    }
    hist
}
