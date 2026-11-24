use alloc::{boxed::Box, format, vec::Vec};
use core::cmp::Ordering;

use anyhow::{Context, Result, anyhow, bail};
use iced_x86::{
    CpuidFeature, Decoder, DecoderOptions, DecoratorKind, FlowControl, FormatterOutput,
    FormatterTextKind, GasFormatter, Instruction, InstructionInfoFactory, IntelFormatter,
    MasmFormatter, Mnemonic, NasmFormatter, NumberKind, OpAccess, OpKind, Register,
};
use object::{Endian as _, Object as _, ObjectSection as _, elf, pe};

use crate::{
    arch::{
        Arch, LogicalAbi, LogicalFlow, LogicalFlowKind, LogicalRegister, OPCODE_DATA,
        RelocationOverride, RelocationOverrideTarget,
    },
    diff::{DiffObjConfig, X86Formatter, display::InstructionPart},
    obj::{
        InstructionArg, InstructionArgValue, InstructionRef, Relocation, RelocationFlags,
        ResolvedInstructionRef, Section, Symbol,
    },
};

#[derive(Debug)]
pub struct ArchX86 {
    arch: Architecture,
    endianness: object::Endianness,
}

#[derive(Debug)]
enum Architecture {
    X86,
    X86_64,
}

impl ArchX86 {
    pub fn new(object: &object::File) -> Result<Self> {
        let arch = match object.architecture() {
            object::Architecture::I386 => Architecture::X86,
            object::Architecture::X86_64 => Architecture::X86_64,
            _ => bail!("Unsupported architecture for ArchX86: {:?}", object.architecture()),
        };
        Ok(Self { arch, endianness: object.endianness() })
    }

    /// 32-bit x86, for objects not read through the `object` crate (OMF).
    pub fn new_i386() -> Self {
        Self { arch: Architecture::X86, endianness: object::Endianness::Little }
    }

    fn decoder<'a>(&self, code: &'a [u8], address: u64) -> Decoder<'a> {
        Decoder::with_ip(
            match self.arch {
                Architecture::X86 => 32,
                Architecture::X86_64 => 64,
            },
            code,
            address,
            DecoderOptions::NONE,
        )
    }

    fn formatter(&self, diff_config: &DiffObjConfig) -> Box<dyn iced_x86::Formatter> {
        let mut formatter: Box<dyn iced_x86::Formatter> = match diff_config.x86_formatter {
            X86Formatter::Intel => Box::new(IntelFormatter::new()),
            X86Formatter::Gas => Box::new(GasFormatter::new()),
            X86Formatter::Nasm => Box::new(NasmFormatter::new()),
            X86Formatter::Masm => Box::new(MasmFormatter::new()),
        };
        formatter.options_mut().set_space_after_operand_separator(diff_config.space_between_args);
        formatter
    }

    fn reloc_size(&self, flags: RelocationFlags) -> Option<usize> {
        match self.arch {
            Architecture::X86 => match flags {
                RelocationFlags::Coff(typ) => match typ {
                    pe::IMAGE_REL_I386_DIR16 | pe::IMAGE_REL_I386_REL16 => Some(2),
                    pe::IMAGE_REL_I386_DIR32 | pe::IMAGE_REL_I386_REL32 => Some(4),
                    _ => None,
                },
                RelocationFlags::Elf(typ) => match typ {
                    elf::R_386_32
                    | elf::R_386_PC32
                    | elf::R_386_GOT32
                    | elf::R_386_PLT32
                    | elf::R_386_GOTOFF
                    | elf::R_386_GOTPC => Some(4),
                    elf::R_386_16 => Some(2),
                    _ => None,
                },
            },
            Architecture::X86_64 => match flags {
                RelocationFlags::Coff(typ) => match typ {
                    pe::IMAGE_REL_AMD64_ADDR32NB
                    | pe::IMAGE_REL_AMD64_REL32
                    | pe::IMAGE_REL_AMD64_REL32_1
                    | pe::IMAGE_REL_AMD64_REL32_2
                    | pe::IMAGE_REL_AMD64_REL32_3
                    | pe::IMAGE_REL_AMD64_REL32_4
                    | pe::IMAGE_REL_AMD64_REL32_5
                    | pe::IMAGE_REL_AMD64_SECREL => Some(4),
                    pe::IMAGE_REL_AMD64_ADDR64 => Some(8),
                    _ => None,
                },
                RelocationFlags::Elf(typ) => match typ {
                    elf::R_X86_64_PC32 => Some(4),
                    elf::R_X86_64_64 => Some(8),
                    _ => None,
                },
            },
        }
    }
}

impl Arch for ArchX86 {
    fn scan_instructions_internal(
        &self,
        address: u64,
        code: &[u8],
        _section_index: usize,
        relocations: &[Relocation],
        diff_config: &DiffObjConfig,
    ) -> Result<Vec<InstructionRef>> {
        let mut out = Vec::with_capacity(code.len() / 2);
        let mut decoder = self.decoder(code, address);
        let mut instruction = Instruction::default();
        let mut reloc_iter = relocations.iter().peekable();
        'outer: while decoder.can_decode() {
            let address = decoder.ip();
            while let Some(reloc) = reloc_iter.peek() {
                match reloc.address.cmp(&address) {
                    Ordering::Less => {
                        reloc_iter.next();
                    }
                    Ordering::Equal => {
                        // If the instruction starts at a relocation, it's inline data
                        let size = self.reloc_size(reloc.flags).with_context(|| {
                            format!("Unsupported inline x86 relocation {:?}", reloc.flags)
                        })?;
                        if decoder.set_position(decoder.position() + size).is_ok() {
                            decoder.set_ip(address + size as u64);
                            out.push(InstructionRef {
                                address,
                                size: size as u8,
                                opcode: OPCODE_DATA,
                                branch_dest: None,
                            });

                            reloc_iter.next();

                            // support .byte arrays after jump tables (they're typically known as indirect tables)

                            let indirect_array_address = address.wrapping_add(size as u64);
                            let indirect_array_pos = decoder.position();

                            let max_size = code.len().saturating_sub(indirect_array_pos);

                            let indirect_array_size = reloc_iter
                                .peek()
                                .map(|next_reloc| {
                                    next_reloc.address.saturating_sub(indirect_array_address)
                                        as usize
                                })
                                .unwrap_or(max_size)
                                .min(max_size);

                            if indirect_array_size > 0 && !diff_config.x86_decode_after_jump_table {
                                for i in 0..indirect_array_size {
                                    out.push(InstructionRef {
                                        address: indirect_array_address + i as u64,
                                        size: 1,
                                        opcode: OPCODE_DATA,
                                        branch_dest: None,
                                    });
                                }
                                // move decoder to after the array (there can be multiple jump+indirect tables in one function)
                                let _ =
                                    decoder.set_position(indirect_array_pos + indirect_array_size);
                                decoder.set_ip(indirect_array_address + indirect_array_size as u64);
                            }

                            continue 'outer;
                        }
                    }
                    Ordering::Greater => break,
                }
            }
            decoder.decode_out(&mut instruction);
            let branch_dest = match instruction.op0_kind() {
                OpKind::NearBranch16 => Some(instruction.near_branch16() as u64),
                OpKind::NearBranch32 => Some(instruction.near_branch32() as u64),
                OpKind::NearBranch64 => Some(instruction.near_branch64()),
                _ => None,
            };
            out.push(InstructionRef {
                address,
                size: instruction.len() as u8,
                opcode: instruction.mnemonic() as u16,
                branch_dest,
            });
        }
        // Strip trailing int3 instructions (alignment padding) for x64
        if matches!(self.arch, Architecture::X86_64) {
            while out.last().is_some_and(|i| i.opcode == iced_x86::Mnemonic::Int3 as u16) {
                out.pop();
            }
        }
        Ok(out)
    }

    fn display_instruction(
        &self,
        resolved: ResolvedInstructionRef,
        diff_config: &DiffObjConfig,
        cb: &mut dyn FnMut(InstructionPart) -> Result<()>,
    ) -> Result<()> {
        if resolved.ins_ref.opcode == OPCODE_DATA {
            let (mnemonic, imm) = match resolved.ins_ref.size {
                1 => (".byte", resolved.code[0] as u64),
                2 => (".word", self.endianness.read_u16(resolved.code.try_into()?) as u64),
                4 => (".dword", self.endianness.read_u32(resolved.code.try_into()?) as u64),
                _ => bail!("Unsupported x86 inline data size {}", resolved.ins_ref.size),
            };
            cb(InstructionPart::opcode(mnemonic, OPCODE_DATA))?;
            if resolved.relocation.is_some() {
                cb(InstructionPart::reloc())?;
            } else {
                cb(InstructionPart::unsigned(imm))?;
            }
            return Ok(());
        }

        let mut decoder = self.decoder(resolved.code, resolved.ins_ref.address);
        let mut formatter = self.formatter(diff_config);
        let mut instruction = Instruction::default();
        decoder.decode_out(&mut instruction);

        // Determine where to insert relocation in instruction output.
        // We replace the immediate or displacement with a placeholder value since the formatter
        // doesn't provide enough information to know which number is the displacement inside a
        // memory operand.
        let mut reloc_replace = None;
        if let Some(reloc) = resolved.relocation {
            const PLACEHOLDER: u64 = 0x7BDE3E7D; // chosen by fair dice roll. guaranteed to be random.
            let reloc_offset = reloc.relocation.address - resolved.ins_ref.address;
            let reloc_size = self.reloc_size(reloc.relocation.flags).unwrap_or(usize::MAX);
            let offsets = decoder.get_constant_offsets(&instruction);
            if reloc_offset == offsets.displacement_offset() as u64
                && reloc_size == offsets.displacement_size()
            {
                instruction.set_memory_displacement64(PLACEHOLDER);
                // Formatter always writes the displacement as Int32
                reloc_replace = Some((OpKind::Memory, 4, PLACEHOLDER));
            } else if reloc_offset == offsets.immediate_offset() as u64
                && reloc_size == offsets.immediate_size()
            {
                let is_branch = matches!(
                    instruction.op0_kind(),
                    OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
                );
                let op_kind = if is_branch {
                    instruction.op0_kind()
                } else {
                    match reloc_size {
                        2 => OpKind::Immediate16,
                        4 => OpKind::Immediate32,
                        8 => OpKind::Immediate64,
                        _ => OpKind::default(),
                    }
                };
                if is_branch {
                    instruction.set_near_branch64(PLACEHOLDER);
                } else {
                    instruction.set_immediate32(PLACEHOLDER as u32);
                }
                reloc_replace = Some((op_kind, reloc_size, PLACEHOLDER));
            }
        }

        let mut output =
            InstructionFormatterOutput { cb, reloc_replace, error: None, skip_next: false };
        formatter.format(&instruction, &mut output);
        if let Some(error) = output.error.take() {
            return Err(error);
        }
        Ok(())
    }

    fn relocation_override(
        &self,
        _file: &object::File<'_>,
        section: &object::Section,
        address: u64,
        relocation: &object::Relocation,
    ) -> Result<Option<RelocationOverride>> {
        if !relocation.has_implicit_addend() {
            return Ok(None);
        }
        let addend = match self.arch {
            Architecture::X86 => match relocation.flags() {
                object::RelocationFlags::Coff {
                    typ: pe::IMAGE_REL_I386_DIR32 | pe::IMAGE_REL_I386_REL32,
                }
                | object::RelocationFlags::Elf {
                    r_type:
                        elf::R_386_32
                        | elf::R_386_PC32
                        | elf::R_386_GOT32
                        | elf::R_386_PLT32
                        | elf::R_386_GOTOFF
                        | elf::R_386_GOTPC,
                } => {
                    let data =
                        section.data()?[address as usize..address as usize + 4].try_into()?;
                    self.endianness.read_i32(data) as i64
                }
                flags => bail!("Unsupported x86 implicit relocation {flags:?}"),
            },
            Architecture::X86_64 => match relocation.flags() {
                object::RelocationFlags::Coff {
                    typ:
                        pe::IMAGE_REL_AMD64_ADDR32NB
                        | pe::IMAGE_REL_AMD64_REL32
                        | pe::IMAGE_REL_AMD64_REL32_1
                        | pe::IMAGE_REL_AMD64_REL32_2
                        | pe::IMAGE_REL_AMD64_REL32_3
                        | pe::IMAGE_REL_AMD64_REL32_4
                        | pe::IMAGE_REL_AMD64_REL32_5
                        | pe::IMAGE_REL_AMD64_SECREL,
                }
                | object::RelocationFlags::Elf { r_type: elf::R_X86_64_32 | elf::R_X86_64_PC32 } => {
                    let data =
                        section.data()?[address as usize..address as usize + 4].try_into()?;
                    self.endianness.read_i32(data) as i64
                }
                object::RelocationFlags::Coff { typ: pe::IMAGE_REL_AMD64_ADDR64 }
                | object::RelocationFlags::Elf { r_type: elf::R_X86_64_64 } => {
                    let data =
                        section.data()?[address as usize..address as usize + 8].try_into()?;
                    self.endianness.read_i64(data)
                }
                flags => bail!("Unsupported x86-64 implicit relocation {flags:?}"),
            },
        };
        Ok(Some(RelocationOverride { target: RelocationOverrideTarget::Keep, addend }))
    }

    fn reloc_name(&self, flags: RelocationFlags) -> Option<&'static str> {
        match self.arch {
            Architecture::X86 => match flags {
                RelocationFlags::Coff(typ) => match typ {
                    pe::IMAGE_REL_I386_DIR32 => Some("IMAGE_REL_I386_DIR32"),
                    pe::IMAGE_REL_I386_REL32 => Some("IMAGE_REL_I386_REL32"),
                    _ => None,
                },
                RelocationFlags::Elf(typ) => match typ {
                    elf::R_386_32 => Some("R_386_32"),
                    elf::R_386_PC32 => Some("R_386_PC32"),
                    elf::R_386_GOT32 => Some("R_386_GOT32"),
                    elf::R_386_PLT32 => Some("R_386_PLT32"),
                    elf::R_386_GOTOFF => Some("R_386_GOTOFF"),
                    elf::R_386_GOTPC => Some("R_386_GOTPC"),
                    elf::R_386_16 => Some("R_386_16"),
                    _ => None,
                },
            },
            Architecture::X86_64 => match flags {
                RelocationFlags::Coff(typ) => match typ {
                    pe::IMAGE_REL_AMD64_ADDR64 => Some("IMAGE_REL_AMD64_ADDR64"),
                    pe::IMAGE_REL_AMD64_ADDR32NB => Some("IMAGE_REL_AMD64_ADDR32NB"),
                    pe::IMAGE_REL_AMD64_REL32 => Some("IMAGE_REL_AMD64_REL32"),
                    pe::IMAGE_REL_AMD64_REL32_1 => Some("IMAGE_REL_AMD64_REL32_1"),
                    pe::IMAGE_REL_AMD64_REL32_2 => Some("IMAGE_REL_AMD64_REL32_2"),
                    pe::IMAGE_REL_AMD64_REL32_3 => Some("IMAGE_REL_AMD64_REL32_3"),
                    pe::IMAGE_REL_AMD64_REL32_4 => Some("IMAGE_REL_AMD64_REL32_4"),
                    pe::IMAGE_REL_AMD64_REL32_5 => Some("IMAGE_REL_AMD64_REL32_5"),
                    pe::IMAGE_REL_AMD64_SECREL => Some("IMAGE_REL_AMD64_SECREL"),
                    _ => None,
                },
                _ => None,
            },
        }
    }

    fn data_reloc_size(&self, flags: RelocationFlags) -> usize {
        self.reloc_size(flags).unwrap_or(1)
    }

    fn logical_abi(&self) -> Option<LogicalAbi> {
        match self.arch {
            // Register (Delphi), fastcall and thiscall pass arguments in eax / edx / ecx; all
            // conventions clobber them and return in eax.
            Architecture::X86 => Some(LogicalAbi {
                call_registers: &[REG_EAX, REG_ECX, REG_EDX],
                return_registers: &[REG_EAX],
                callee_saved: &[REG_EBX, REG_EBP, REG_ESI, REG_EDI],
            }),
            Architecture::X86_64 => None,
        }
    }

    fn logical_register(&self, arg: &InstructionArg) -> Option<LogicalRegister> {
        let InstructionArg::Value(InstructionArgValue::Opaque(name)) = arg else { return None };
        let name = name.strip_prefix('%').unwrap_or(name);
        let (family, part) = match name.to_ascii_lowercase().as_str() {
            "eax" => (REG_EAX, PART_32),
            "ecx" => (REG_ECX, PART_32),
            "edx" => (REG_EDX, PART_32),
            "ebx" => (REG_EBX, PART_32),
            "ebp" => (REG_EBP, PART_32),
            "esi" => (REG_ESI, PART_32),
            "edi" => (REG_EDI, PART_32),
            "ax" => (REG_EAX, PART_16),
            "cx" => (REG_ECX, PART_16),
            "dx" => (REG_EDX, PART_16),
            "bx" => (REG_EBX, PART_16),
            "bp" => (REG_EBP, PART_16),
            "si" => (REG_ESI, PART_16),
            "di" => (REG_EDI, PART_16),
            "al" => (REG_EAX, PART_LOW8),
            "cl" => (REG_ECX, PART_LOW8),
            "dl" => (REG_EDX, PART_LOW8),
            "bl" => (REG_EBX, PART_LOW8),
            "ah" => (REG_EAX, PART_HIGH8),
            "ch" => (REG_ECX, PART_HIGH8),
            "dh" => (REG_EDX, PART_HIGH8),
            "bh" => (REG_EBX, PART_HIGH8),
            _ => return None,
        };
        Some(LogicalRegister { family, part })
    }

    fn logical_flow(
        &self,
        resolved: ResolvedInstructionRef,
        _diff_config: &DiffObjConfig,
    ) -> Result<LogicalFlow> {
        let mut flow = LogicalFlow::default();
        if resolved.ins_ref.opcode == OPCODE_DATA {
            return Ok(flow);
        }
        let mut decoder = self.decoder(resolved.code, resolved.ins_ref.address);
        let mut instruction = Instruction::default();
        decoder.decode_out(&mut instruction);
        let mut factory = InstructionInfoFactory::new();
        let info = factory.info(&instruction);

        flow.kind = match instruction.flow_control() {
            FlowControl::Next => LogicalFlowKind::Normal,
            FlowControl::Call | FlowControl::IndirectCall => LogicalFlowKind::Call,
            FlowControl::Return => LogicalFlowKind::Return,
            _ => LogicalFlowKind::Branch,
        };
        flow.reads_flags = instruction.rflags_read() != 0;
        flow.writes_flags = instruction.rflags_modified() != 0;
        for used in info.used_memory() {
            let (read, write) = access_read_write(used.access());
            flow.reads_memory |= read;
            flow.writes_memory |= write;
        }

        // `xor eax, eax` and friends do not depend on the register's old value
        let zero_idiom =
            matches!(instruction.mnemonic(), Mnemonic::Xor | Mnemonic::Sub | Mnemonic::Sbb)
                && instruction.op_count() == 2
                && instruction.op0_kind() == OpKind::Register
                && instruction.op1_kind() == OpKind::Register
                && instruction.op0_register() == instruction.op1_register();

        // Explicit operands first, in operand order, so that the reads of the two sides pair up
        // by position
        let mut explicit = Vec::<Register>::new();
        let mut writes = Vec::<Register>::new();
        for op in 0..instruction.op_count() {
            match instruction.op_kind(op) {
                OpKind::Register => {
                    let reg = instruction.op_register(op);
                    explicit.push(reg);
                    let (read, write) = access_read_write(info.op_access(op));
                    if read && !zero_idiom {
                        push_read(&mut flow, reg);
                    }
                    if write {
                        writes.push(reg);
                    }
                }
                OpKind::Memory => {
                    for reg in [instruction.memory_base(), instruction.memory_index()] {
                        if reg != Register::None {
                            explicit.push(reg);
                            push_read(&mut flow, reg);
                        }
                    }
                }
                _ => {}
            }
        }
        // Implicit registers (cdq, rep movsd, mul, push's esp, ...) are fixed by the instruction
        for used in info.used_registers() {
            if explicit.contains(&used.register()) {
                continue;
            }
            let (read, write) = access_read_write(used.access());
            if read {
                push_read(&mut flow, used.register());
            }
            if write {
                writes.push(used.register());
            }
        }
        for reg in writes {
            if logical_register(reg).is_some() {
                push_logical(&mut flow.writes, reg);
            } else if let Some(id) = fixed_register(reg) {
                push_fixed(&mut flow.fixed_writes, id);
            }
        }
        // Every x87 / MMX instruction depends on and changes the register stack (its top, the
        // tag and status words, the control word's rounding), whether or not it names a register
        if instruction.cpuid_features().iter().any(|f| {
            matches!(
                f,
                CpuidFeature::FPU
                    | CpuidFeature::FPU287
                    | CpuidFeature::FPU287XL_ONLY
                    | CpuidFeature::FPU387
                    | CpuidFeature::FPU387SL_ONLY
                    | CpuidFeature::MMX
                    | CpuidFeature::D3NOW
                    | CpuidFeature::D3NOWEXT
            )
        }) {
            push_fixed(&mut flow.fixed_reads, FIXED_FPU_STACK);
            push_fixed(&mut flow.fixed_writes, FIXED_FPU_STACK);
        }
        Ok(flow)
    }

    fn infer_function_size(
        &self,
        symbol: &Symbol,
        section: &Section,
        next_address: u64,
    ) -> Result<u64> {
        let Ok(size) = (next_address - symbol.address).try_into() else {
            return Ok(next_address.saturating_sub(symbol.address));
        };
        let Some(code) = section.data_range(symbol.address, size) else {
            return Ok(0);
        };
        // Decode instructions to find the last non-NOP instruction
        let mut decoder = self.decoder(code, symbol.address);
        let mut instruction = Instruction::default();
        let mut new_address = 0;
        let mut reloc_iter = section.relocations.iter().peekable();
        'outer: while decoder.can_decode() {
            let address = decoder.ip();
            while let Some(reloc) = reloc_iter.peek() {
                match reloc.address.cmp(&address) {
                    Ordering::Less => {
                        reloc_iter.next();
                    }
                    Ordering::Equal => {
                        // If the instruction starts at a relocation, it's inline data
                        let reloc_size = self.reloc_size(reloc.flags).with_context(|| {
                            format!("Unsupported inline x86 relocation {:?}", reloc.flags)
                        })?;
                        if decoder.set_position(decoder.position() + reloc_size).is_ok() {
                            new_address = address + reloc_size as u64;
                            decoder.set_ip(new_address);
                            continue 'outer;
                        }
                    }
                    Ordering::Greater => break,
                }
            }
            decoder.decode_out(&mut instruction);
            if instruction.mnemonic() != iced_x86::Mnemonic::Nop {
                new_address = instruction.next_ip();
            }
        }
        Ok(new_address.saturating_sub(symbol.address))
    }
}

struct InstructionFormatterOutput<'a> {
    cb: &'a mut dyn FnMut(InstructionPart<'_>) -> Result<()>,
    reloc_replace: Option<(OpKind, usize, u64)>,
    error: Option<anyhow::Error>,
    skip_next: bool,
}

impl InstructionFormatterOutput<'_> {
    fn push_signed(&mut self, mut value: i64) {
        if self.error.is_some() {
            return;
        }
        // The formatter writes the '-' operator and then gives us a negative value,
        // so convert it to a positive value to avoid double negatives
        if value < 0 {
            value = value.wrapping_abs();
        }
        if let Err(e) = (self.cb)(InstructionPart::signed(value)) {
            self.error = Some(e);
        }
    }
}

const REG_EAX: u8 = 0;
const REG_ECX: u8 = 1;
const REG_EDX: u8 = 2;
const REG_EBX: u8 = 3;
const REG_EBP: u8 = 5;
const REG_ESI: u8 = 6;
const REG_EDI: u8 = 7;
const PART_32: u8 = 0;
const PART_16: u8 = 1;
const PART_LOW8: u8 = 2;
const PART_HIGH8: u8 = 3;

/// The renamable 32-bit general register `reg` belongs to (not esp).
fn logical_register(reg: Register) -> Option<LogicalRegister> {
    let family = match reg.full_register32() {
        Register::EAX => REG_EAX,
        Register::ECX => REG_ECX,
        Register::EDX => REG_EDX,
        Register::EBX => REG_EBX,
        Register::EBP => REG_EBP,
        Register::ESI => REG_ESI,
        Register::EDI => REG_EDI,
        _ => return None,
    };
    let part = match reg {
        Register::AH | Register::CH | Register::DH | Register::BH => PART_HIGH8,
        _ => match reg.size() {
            4 => PART_32,
            2 => PART_16,
            1 => PART_LOW8,
            _ => return None,
        },
    };
    Some(LogicalRegister { family, part })
}

fn push_logical(out: &mut Vec<LogicalRegister>, reg: Register) {
    if let Some(reg) = logical_register(reg) {
        out.push(reg);
    }
}

/// `LogicalFlow::fixed_*` id of the x87 register stack (ST0-ST7, aliased by MM0-MM7).
const FIXED_FPU_STACK: u16 = u16::MAX;

/// The `LogicalFlow::fixed_*` id of a register that is not renamed: the stack pointer, the
/// x87 stack, segment and vector registers.
fn fixed_register(reg: Register) -> Option<u16> {
    if reg == Register::None || logical_register(reg).is_some() {
        return None;
    }
    if reg.is_st() || reg.is_mm() {
        return Some(FIXED_FPU_STACK);
    }
    Some(reg.full_register() as u16)
}

fn push_fixed(out: &mut Vec<u16>, id: u16) {
    if !out.contains(&id) {
        out.push(id);
    }
}

/// A register read: renamable ones in `reads`, the others in `fixed_reads`.
fn push_read(flow: &mut LogicalFlow, reg: Register) {
    if logical_register(reg).is_some() {
        push_logical(&mut flow.reads, reg);
    } else if let Some(id) = fixed_register(reg) {
        push_fixed(&mut flow.fixed_reads, id);
    }
}

/// (reads, writes) of an operand access. A conditional write keeps the old value on one path,
/// so it reads it too.
fn access_read_write(access: OpAccess) -> (bool, bool) {
    match access {
        OpAccess::Read | OpAccess::CondRead => (true, false),
        OpAccess::Write => (false, true),
        OpAccess::CondWrite | OpAccess::ReadWrite | OpAccess::ReadCondWrite => (true, true),
        OpAccess::None | OpAccess::NoMemAccess => (false, false),
    }
}

impl FormatterOutput for InstructionFormatterOutput<'_> {
    fn write(&mut self, text: &str, kind: FormatterTextKind) {
        if self.error.is_some() {
            return;
        }
        // Skip whitespace after the mnemonic
        if self.skip_next {
            self.skip_next = false;
            if kind == FormatterTextKind::Text && text == " " {
                return;
            }
        }
        match kind {
            FormatterTextKind::Text | FormatterTextKind::Punctuation => {
                if let Err(e) = (self.cb)(InstructionPart::basic(text)) {
                    self.error = Some(e);
                }
            }
            FormatterTextKind::Prefix
            | FormatterTextKind::Keyword
            | FormatterTextKind::Operator => {
                if let Err(e) = (self.cb)(InstructionPart::opaque(text)) {
                    self.error = Some(e);
                }
            }
            _ => self.error = Some(anyhow!("x86: Unsupported FormatterTextKind {:?}", kind)),
        }
    }

    fn write_mnemonic(&mut self, instruction: &Instruction, text: &str) {
        if self.error.is_some() {
            return;
        }
        if let Err(e) = (self.cb)(InstructionPart::opcode(text, instruction.mnemonic() as u16)) {
            self.error = Some(e);
        }
        // Skip whitespace after the mnemonic
        self.skip_next = true;
    }

    fn write_number(
        &mut self,
        instruction: &Instruction,
        _operand: u32,
        instruction_operand: Option<u32>,
        _text: &str,
        value: u64,
        number_kind: NumberKind,
        kind: FormatterTextKind,
    ) {
        if self.error.is_some() {
            return;
        }

        if let (Some(operand), Some((target_op_kind, reloc_size, target_value))) =
            (instruction_operand, self.reloc_replace)
        {
            #[allow(clippy::match_like_matches_macro)]
            if instruction.op_kind(operand) == target_op_kind
                && match (number_kind, reloc_size) {
                    (NumberKind::Int8 | NumberKind::UInt8, 1)
                    | (NumberKind::Int16 | NumberKind::UInt16, 2)
                    | (NumberKind::Int32 | NumberKind::UInt32, 4)
                    | (NumberKind::Int64 | NumberKind::UInt64, 4) // x86_64
                    | (NumberKind::Int64 | NumberKind::UInt64, 8) => true,
                    _ => false,
                }
                && value == target_value
            {
                if let Err(e) = (self.cb)(InstructionPart::reloc()) {
                    self.error = Some(e);
                }
                return;
            }
        }

        if let FormatterTextKind::LabelAddress | FormatterTextKind::FunctionAddress = kind {
            if let Err(e) = (self.cb)(InstructionPart::branch_dest(value)) {
                self.error = Some(e);
            }
            return;
        }

        match number_kind {
            NumberKind::Int8 => self.push_signed(value as i8 as i64),
            NumberKind::Int16 => self.push_signed(value as i16 as i64),
            NumberKind::Int32 => self.push_signed(value as i32 as i64),
            NumberKind::Int64 => self.push_signed(value as i64),
            NumberKind::UInt8 | NumberKind::UInt16 | NumberKind::UInt32 | NumberKind::UInt64 => {
                if let Err(e) = (self.cb)(InstructionPart::unsigned(value)) {
                    self.error = Some(e);
                }
            }
        }
    }

    fn write_decorator(
        &mut self,
        _instruction: &Instruction,
        _operand: u32,
        _instruction_operand: Option<u32>,
        text: &str,
        _decorator: DecoratorKind,
    ) {
        if self.error.is_some() {
            return;
        }
        if let Err(e) = (self.cb)(InstructionPart::basic(text)) {
            self.error = Some(e);
        }
    }

    fn write_register(
        &mut self,
        _instruction: &Instruction,
        _operand: u32,
        _instruction_operand: Option<u32>,
        text: &str,
        _register: Register,
    ) {
        if self.error.is_some() {
            return;
        }
        if let Err(e) = (self.cb)(InstructionPart::opaque(text)) {
            self.error = Some(e);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::obj::{Relocation, ResolvedRelocation};

    fn flow(code: &[u8]) -> LogicalFlow {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let opcode =
            arch.scan_instructions_internal(0, code, 0, &[], &DiffObjConfig::default()).unwrap()[0]
                .opcode;
        arch.logical_flow(
            ResolvedInstructionRef {
                ins_ref: InstructionRef {
                    address: 0,
                    size: code.len() as u8,
                    opcode,
                    branch_dest: None,
                },
                code,
                ..Default::default()
            },
            &DiffObjConfig::default(),
        )
        .unwrap()
    }

    fn reg(family: u8, part: u8) -> LogicalRegister { LogicalRegister { family, part } }

    #[test]
    fn test_logical_flow() {
        // mov eax, [ebx+esi*4+8]: reads ebx then esi, writes eax
        let f = flow(&[0x8b, 0x44, 0xb3, 0x08]);
        assert_eq!(f.reads, [reg(REG_EBX, PART_32), reg(REG_ESI, PART_32)]);
        assert_eq!(f.writes, [reg(REG_EAX, PART_32)]);
        assert!(f.reads_memory && !f.writes_memory);
        // add [eax], dl: reads eax (address) and dl, writes memory and flags
        let f = flow(&[0x00, 0x10]);
        assert_eq!(f.reads, [reg(REG_EAX, PART_32), reg(REG_EDX, PART_LOW8)]);
        assert!(f.writes.is_empty() && f.writes_memory && f.writes_flags);
        // xor eax, eax does not read eax
        let f = flow(&[0x33, 0xc0]);
        assert!(f.reads.is_empty());
        assert_eq!(f.writes, [reg(REG_EAX, PART_32)]);
        // cdq: implicit read of eax, write of edx
        let f = flow(&[0x99]);
        assert_eq!(f.reads, [reg(REG_EAX, PART_32)]);
        assert_eq!(f.writes, [reg(REG_EDX, PART_32)]);
        // push esi: esp is not tracked; writes memory
        let f = flow(&[0x56]);
        assert_eq!(f.reads, [reg(REG_ESI, PART_32)]);
        assert!(f.writes.is_empty() && f.writes_memory);
        // ... but it reads and changes esp, which is fixed
        let esp = fixed_register(Register::ESP).unwrap();
        assert!(f.fixed_reads.contains(&esp));
        assert_eq!(f.fixed_writes, [esp]);
        // lea eax, [esp+8]: a fixed read of esp
        let f = flow(&[0x8d, 0x44, 0x24, 0x08]);
        assert!(f.fixed_reads.contains(&esp));
        assert!(f.fixed_writes.is_empty());
        // fmul dword ptr [esi+0x24], fptan, fld1: all use the x87 stack
        for code in [&[0xd8, 0x4e, 0x24][..], &[0xd9, 0xf2], &[0xd9, 0xe8]] {
            let f = flow(code);
            assert!(f.fixed_reads.contains(&FIXED_FPU_STACK), "{code:x?}");
            assert!(f.fixed_writes.contains(&FIXED_FPU_STACK), "{code:x?}");
        }
        // mov ecx, esi: no fixed registers
        let f = flow(&[0x8b, 0xce]);
        assert!(f.fixed_reads.is_empty() && f.fixed_writes.is_empty());
        // call rel32 / ret
        assert_eq!(flow(&[0xe8, 0, 0, 0, 0]).kind, LogicalFlowKind::Call);
        assert_eq!(flow(&[0xc3]).kind, LogicalFlowKind::Return);
    }

    #[test]
    fn test_scan_instructions() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [
            0xc7, 0x85, 0x68, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x04, 0x85, 0x00,
            0x00, 0x00, 0x00,
        ];
        let scanned =
            arch.scan_instructions_internal(0, &code, 0, &[], &DiffObjConfig::default()).unwrap();
        assert_eq!(scanned.len(), 2);
        assert_eq!(scanned[0].address, 0);
        assert_eq!(scanned[0].size, 10);
        assert_eq!(scanned[0].opcode, iced_x86::Mnemonic::Mov as u16);
        assert_eq!(scanned[0].branch_dest, None);
        assert_eq!(scanned[1].address, 10);
        assert_eq!(scanned[1].size, 7);
        assert_eq!(scanned[1].opcode, iced_x86::Mnemonic::Mov as u16);
        assert_eq!(scanned[1].branch_dest, None);
    }

    #[test]
    fn test_process_instruction() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0xc7, 0x85, 0x68, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Mov as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 10, opcode, branch_dest: None },
                code: &code,
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode("mov", opcode),
            InstructionPart::opaque("dword"),
            InstructionPart::basic(" "),
            InstructionPart::opaque("ptr"),
            InstructionPart::basic(" "),
            InstructionPart::basic("["),
            InstructionPart::opaque("ebp"),
            InstructionPart::opaque("-"),
            InstructionPart::signed(152i64),
            InstructionPart::basic("]"),
            InstructionPart::basic(","),
            InstructionPart::basic(" "),
            InstructionPart::unsigned(0u64),
        ]);
    }

    #[test]
    fn test_process_instruction_with_reloc_1() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0xc7, 0x85, 0x68, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Mov as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 10, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_I386_DIR32),
                        address: 0x1234 + 6,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode("mov", opcode),
            InstructionPart::opaque("dword"),
            InstructionPart::basic(" "),
            InstructionPart::opaque("ptr"),
            InstructionPart::basic(" "),
            InstructionPart::basic("["),
            InstructionPart::opaque("ebp"),
            InstructionPart::opaque("-"),
            InstructionPart::signed(152i64),
            InstructionPart::basic("]"),
            InstructionPart::basic(","),
            InstructionPart::basic(" "),
            InstructionPart::reloc(),
        ]);
    }

    #[test]
    fn test_process_instruction_with_reloc_2() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0x8b, 0x04, 0x85, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Mov as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 7, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_I386_DIR32),
                        address: 0x1234 + 3,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode("mov", opcode),
            InstructionPart::opaque("eax"),
            InstructionPart::basic(","),
            InstructionPart::basic(" "),
            InstructionPart::basic("["),
            InstructionPart::opaque("eax"),
            InstructionPart::opaque("*"),
            InstructionPart::signed(4),
            InstructionPart::opaque("+"),
            InstructionPart::reloc(),
            InstructionPart::basic("]"),
        ]);
    }

    #[test]
    fn test_process_instruction_with_reloc_3() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0xe8, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Call as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 5, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_I386_REL32),
                        address: 0x1234 + 1,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[InstructionPart::opcode("call", opcode), InstructionPart::reloc()]);
    }

    #[test]
    fn test_process_instruction_with_reloc_4() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0x8b, 0x15, 0xa4, 0x21, 0x7e, 0x00];
        let opcode = iced_x86::Mnemonic::Mov as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 6, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_I386_DIR32),
                        address: 0x1234 + 2,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode("mov", opcode),
            InstructionPart::opaque("edx"),
            InstructionPart::basic(","),
            InstructionPart::basic(" "),
            InstructionPart::basic("["),
            InstructionPart::reloc(),
            InstructionPart::basic("]"),
        ]);
    }

    #[test]
    fn test_process_x86_64_instruction_with_reloc_1() {
        let arch = ArchX86 { arch: Architecture::X86_64, endianness: object::Endianness::Little };
        let code = [0x48, 0x8b, 0x05, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Mov as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 7, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_AMD64_REL32),
                        address: 0x1234 + 3,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode("mov", opcode),
            InstructionPart::opaque("rax"),
            InstructionPart::basic(","),
            InstructionPart::basic(" "),
            InstructionPart::basic("["),
            InstructionPart::reloc(),
            InstructionPart::basic("]"),
        ]);
    }

    #[test]
    fn test_process_x86_64_instruction_with_reloc_2() {
        let arch = ArchX86 { arch: Architecture::X86_64, endianness: object::Endianness::Little };
        let code = [0xe8, 0x00, 0x00, 0x00, 0x00];
        let opcode = iced_x86::Mnemonic::Call as u16;
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef { address: 0x1234, size: 5, opcode, branch_dest: None },
                code: &code,
                relocation: Some(ResolvedRelocation {
                    relocation: &Relocation {
                        flags: RelocationFlags::Coff(pe::IMAGE_REL_AMD64_REL32),
                        address: 0x1234 + 1,
                        target_symbol: 0,
                        addend: 0,
                    },
                    symbol: &Default::default(),
                }),
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[InstructionPart::opcode("call", opcode), InstructionPart::reloc()]);
    }

    #[test]
    fn test_display_1_byte_inline_data() {
        let arch = ArchX86 { arch: Architecture::X86, endianness: object::Endianness::Little };
        let code = [0xAB];
        let mut parts = Vec::new();
        arch.display_instruction(
            ResolvedInstructionRef {
                ins_ref: InstructionRef {
                    address: 0x1234,
                    size: 1,
                    opcode: OPCODE_DATA,
                    branch_dest: None,
                },
                code: &code,
                ..Default::default()
            },
            &DiffObjConfig::default(),
            &mut |part| {
                parts.push(part.into_static());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(parts, &[
            InstructionPart::opcode(".byte", OPCODE_DATA),
            InstructionPart::unsigned(0xABu64),
        ]);
    }
}
