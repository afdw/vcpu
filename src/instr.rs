// RISC-V 64-bits instructions

use crate::{extract_bits, sign_extend};

#[derive(Default)]
struct Decomposition {
    opcode: u64,
    funct_3: u64,
    funct_7: u64,
    rd: u64,
    rs_1: u64,
    rs_2: u64,
    imm: u64,
}

fn decompose_r_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        rd: extract_bits(instr_encoding, 7, 5),
        funct_3: extract_bits(instr_encoding, 12, 3),
        rs_1: extract_bits(instr_encoding, 15, 5),
        rs_2: extract_bits(instr_encoding, 20, 5),
        funct_7: extract_bits(instr_encoding, 25, 7),
        ..Decomposition::default()
    }
}

fn decompose_i_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        rd: extract_bits(instr_encoding, 7, 5),
        funct_3: extract_bits(instr_encoding, 12, 3),
        rs_1: extract_bits(instr_encoding, 15, 5),
        imm: sign_extend(extract_bits(instr_encoding, 20, 12), 12),
        ..Decomposition::default()
    }
}

fn decompose_s_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        funct_3: extract_bits(instr_encoding, 12, 3),
        rs_1: extract_bits(instr_encoding, 15, 5),
        rs_2: extract_bits(instr_encoding, 20, 5),
        imm: sign_extend(
            (extract_bits(instr_encoding, 25, 7) << 5) | extract_bits(instr_encoding, 7, 5),
            12,
        ),
        ..Decomposition::default()
    }
}

fn decompose_b_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        funct_3: extract_bits(instr_encoding, 12, 3),
        rs_1: extract_bits(instr_encoding, 15, 5),
        rs_2: extract_bits(instr_encoding, 20, 5),
        imm: sign_extend(
            (extract_bits(instr_encoding, 31, 1) << 12)
                | (extract_bits(instr_encoding, 7, 1) << 11)
                | (extract_bits(instr_encoding, 25, 6) << 5)
                | (extract_bits(instr_encoding, 8, 4) << 1),
            13,
        ),
        ..Decomposition::default()
    }
}

fn decompose_u_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        rd: extract_bits(instr_encoding, 7, 5),
        imm: extract_bits(instr_encoding, 12, 20) << 12,
        ..Decomposition::default()
    }
}

fn decompose_j_type(instr_encoding: u64) -> Decomposition {
    Decomposition {
        opcode: extract_bits(instr_encoding, 0, 7),
        rd: extract_bits(instr_encoding, 7, 5),
        imm: sign_extend(
            (extract_bits(instr_encoding, 31, 1) << 20)
                | (extract_bits(instr_encoding, 12, 8) << 12)
                | (extract_bits(instr_encoding, 20, 1) << 11)
                | (extract_bits(instr_encoding, 21, 10) << 1),
            21,
        ),
        ..Decomposition::default()
    }
}

#[derive(Debug)]
enum Instr {

}

fn decode(instr_encoding: u64) -> Instr {
}
