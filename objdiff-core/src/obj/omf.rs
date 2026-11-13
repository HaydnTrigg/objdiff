//! Reader for 32-bit Intel OMF objects, as written by Borland Delphi (`dcc32 -J` / `-JP`) and
//! C++Builder.
//!
//! Besides the standard records, Borland compilers place every routine, VMT, RTTI block and
//! literal in its own "virtual segment": a COMDEF record whose data type byte is the index of the
//! SEGDEF that owns it (instead of 0x61 / 0x62 for communal variables). LEDATA and FIXUPP records
//! address a virtual segment with the segment index `0x4000 | n`, where `n` is the position of the
//! COMDEF entry. COMDEF entries also share the external name index space with EXTDEF entries.
//!
//! objdiff's object model is section based, so the reader lays the object out the way a linker
//! would: every virtual segment is appended to the section of its owning segment. Pieces of data
//! that Delphi keeps in the code segment (VMTs, RTTI, string literals, resource strings) are moved
//! to a separate `.rdata` section so they are diffed as data instead of being disassembled.
//! Segments are named after their COFF equivalents (`_TEXT` becomes `.text`) so that OMF objects
//! pair with COFF objects split from the original executable. Fixups become COFF i386 relocations
//! with the addend stored in the section data, like COFF objects.

use alloc::{
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::num::NonZeroU64;

use anyhow::{Context, Result, anyhow, bail, ensure};
use object::pe;

use crate::{
    arch::x86::ArchX86,
    diff::DiffObjConfig,
    obj::{
        Relocation, RelocationFlags, Section, SectionData, SectionKind, Symbol, SymbolFlag,
        SymbolFlagSet, SymbolKind,
    },
};

const THEADR: u8 = 0x80;
const LHEADR: u8 = 0x82;
const COMENT: u8 = 0x88;
const MODEND: u8 = 0x8A;
const MODEND32: u8 = 0x8B;
const EXTDEF: u8 = 0x8C;
const PUBDEF: u8 = 0x90;
const PUBDEF32: u8 = 0x91;
const LNAMES: u8 = 0x96;
const SEGDEF: u8 = 0x98;
const SEGDEF32: u8 = 0x99;
const GRPDEF: u8 = 0x9A;
const FIXUPP: u8 = 0x9C;
const FIXUPP32: u8 = 0x9D;
const LEDATA: u8 = 0xA0;
const LEDATA32: u8 = 0xA1;
const LIDATA: u8 = 0xA2;
const LIDATA32: u8 = 0xA3;
const COMDEF: u8 = 0xB0;
const LEXTDEF: u8 = 0xB4;
const LEXTDEF32: u8 = 0xB5;
const LPUBDEF: u8 = 0xB6;
const LPUBDEF32: u8 = 0xB7;
const LCOMDEF: u8 = 0xB8;
const COMDAT: u8 = 0xC2;
const COMDAT32: u8 = 0xC3;
const LLNAMES: u8 = 0xCA;

/// Segment index bit Borland uses to address a virtual segment (COMDEF entry).
const VIRTUAL_SEGMENT: u16 = 0x4000;

/// Name of the synthetic section that receives data kept in code segments.
const RDATA: &str = ".rdata";

/// Whether `data` looks like an OMF object (starts with a THEADR / LHEADR record).
pub fn is_omf(data: &[u8]) -> bool {
    if data.len() < 5 || !matches!(data[0], THEADR | LHEADR) {
        return false;
    }
    let length = u16::from_le_bytes([data[1], data[2]]) as usize;
    // Record body: name length, name, checksum
    length >= 2 && data[3] as usize + 2 == length && 3 + length <= data.len()
}

struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(data: &'a [u8]) -> Self { Self { data, pos: 0 } }

    fn is_empty(&self) -> bool { self.pos >= self.data.len() }

    fn bytes(&mut self, len: usize) -> Result<&'a [u8]> {
        let bytes = self
            .data
            .get(self.pos..self.pos + len)
            .ok_or_else(|| anyhow!("OMF record truncated at offset {:#x}", self.pos))?;
        self.pos += len;
        Ok(bytes)
    }

    fn rest(&mut self) -> &'a [u8] {
        let rest = &self.data[self.pos.min(self.data.len())..];
        self.pos = self.data.len();
        rest
    }

    fn u8(&mut self) -> Result<u8> { Ok(self.bytes(1)?[0]) }

    fn u16(&mut self) -> Result<u16> { Ok(u16::from_le_bytes(self.bytes(2)?.try_into()?)) }

    fn u32(&mut self) -> Result<u32> { Ok(u32::from_le_bytes(self.bytes(4)?.try_into()?)) }

    /// 16-bit or 32-bit field, depending on the record type.
    fn word(&mut self, is32: bool) -> Result<u32> {
        if is32 { self.u32() } else { self.u16().map(u32::from) }
    }

    /// One or two byte index field.
    fn index(&mut self) -> Result<u16> {
        let first = self.u8()?;
        if first & 0x80 != 0 {
            Ok((((first & 0x7F) as u16) << 8) | self.u8()? as u16)
        } else {
            Ok(first as u16)
        }
    }

    /// Length-prefixed name.
    fn name(&mut self) -> Result<String> {
        let len = self.u8()? as usize;
        Ok(self.bytes(len)?.iter().map(|&c| c as char).collect())
    }

    /// Communal length field of a COMDEF entry.
    fn communal_length(&mut self) -> Result<u64> {
        Ok(match self.u8()? {
            n @ 0..=0x80 => n as u64,
            0x81 => self.u16()? as u64,
            0x84 => {
                let bytes = self.bytes(3)?;
                u32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]) as u64
            }
            0x88 => self.u32()? as u64,
            n => bail!("Invalid COMDEF length prefix {n:#x}"),
        })
    }
}

/// A SEGDEF record or a Borland virtual segment.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
enum SegmentRef {
    Segment(usize),
    Virtual(usize),
}

impl SegmentRef {
    fn from_index(index: u16) -> Result<Self> {
        ensure!(index != 0, "Segment index 0 is not supported");
        Ok(if index & VIRTUAL_SEGMENT != 0 {
            let virt = (index & !VIRTUAL_SEGMENT) as usize;
            SegmentRef::Virtual(virt.checked_sub(1).context("Virtual segment index 0")?)
        } else {
            SegmentRef::Segment(index as usize - 1)
        })
    }
}

struct Segment {
    name: String,
    class: String,
    length: u64,
    align: u64,
    data: Vec<u8>,
}

struct VirtualSegment {
    name: String,
    /// Owning SEGDEF
    segment: usize,
    data: Vec<u8>,
    local: bool,
}

enum External {
    /// EXTDEF / LEXTDEF
    Undefined { name: String, local: bool },
    /// Borland virtual segment
    Virtual(usize),
    /// Communal variable (COMDEF / LCOMDEF with a FAR or NEAR data type)
    Communal { name: String, size: u64, local: bool },
}

struct Public {
    name: String,
    segment: SegmentRef,
    offset: u64,
    local: bool,
}

#[derive(Copy, Clone, Debug)]
enum FixupTarget {
    Segment(SegmentRef),
    Group(usize),
    External(usize),
    Frame,
}

struct Fixup {
    segment: SegmentRef,
    offset: u64,
    self_relative: bool,
    location: u8,
    target: FixupTarget,
    displacement: i64,
}

#[derive(Copy, Clone, Default)]
struct TargetThread {
    method: u8,
    index: u16,
}

#[derive(Default)]
struct OmfObject {
    names: Vec<String>,
    segments: Vec<Segment>,
    groups: Vec<Vec<usize>>,
    virtuals: Vec<VirtualSegment>,
    externals: Vec<External>,
    publics: Vec<Public>,
    fixups: Vec<Fixup>,
}

impl OmfObject {
    fn name(&self, index: u16) -> Result<&str> {
        match index {
            0 => Ok(""),
            n => self
                .names
                .get(n as usize - 1)
                .map(String::as_str)
                .ok_or_else(|| anyhow!("Invalid LNAMES index {n}")),
        }
    }

    fn segment_data(&mut self, segment: SegmentRef) -> Result<&mut Vec<u8>> {
        match segment {
            SegmentRef::Segment(i) => self.segments.get_mut(i).map(|s| &mut s.data),
            SegmentRef::Virtual(i) => self.virtuals.get_mut(i).map(|v| &mut v.data),
        }
        .ok_or_else(|| anyhow!("Invalid segment reference {segment:?}"))
    }

    fn write(&mut self, segment: SegmentRef, offset: u64, bytes: &[u8]) -> Result<()> {
        let data = self.segment_data(segment)?;
        let start = offset as usize;
        let end = start + bytes.len();
        if data.len() < end {
            data.resize(end, 0);
        }
        data[start..end].copy_from_slice(bytes);
        Ok(())
    }
}

fn parse_records(data: &[u8]) -> Result<OmfObject> {
    let mut obj = OmfObject::default();
    let mut target_threads = [TargetThread::default(); 4];
    // Segment and offset of the last LEDATA / LIDATA record, for FIXUPP
    let mut last_data: Option<(SegmentRef, u64)> = None;
    let mut pos = 0;
    while pos + 3 <= data.len() {
        let kind = data[pos];
        let length = u16::from_le_bytes([data[pos + 1], data[pos + 2]]) as usize;
        ensure!(length >= 1 && pos + 3 + length <= data.len(), "OMF record at {pos:#x} truncated");
        // Strip the checksum
        let body = &data[pos + 3..pos + 2 + length];
        let is32 = kind & 1 != 0;
        let mut r = Reader::new(body);
        pos += 3 + length;
        match kind {
            THEADR | LHEADR | COMENT => {}
            LNAMES | LLNAMES => {
                while !r.is_empty() {
                    obj.names.push(r.name()?);
                }
            }
            SEGDEF | SEGDEF32 => {
                let attributes = r.u8()?;
                let alignment = attributes >> 5;
                if alignment == 0 {
                    // Absolute segment: frame number and offset
                    r.u16()?;
                    r.u8()?;
                }
                let mut length = r.word(is32)? as u64;
                if attributes & 2 != 0 && length == 0 {
                    // "Big" segment: 64K or 4G
                    length = if is32 { 1 << 32 } else { 1 << 16 };
                }
                let name = obj.name(r.index()?)?.to_string();
                let class = obj.name(r.index()?)?.to_string();
                let align = match alignment {
                    2 => 2,
                    3 => 16,
                    4 => 256,
                    5 => 4,
                    6 => 4096,
                    _ => 1,
                };
                obj.segments.push(Segment { name, class, length, align, data: Vec::new() });
            }
            GRPDEF => {
                r.index()?;
                let mut segments = Vec::new();
                while !r.is_empty() {
                    if r.u8()? == 0xFF {
                        segments.push(r.index()? as usize - 1);
                    } else {
                        r.index()?;
                    }
                }
                obj.groups.push(segments);
            }
            EXTDEF | LEXTDEF | LEXTDEF32 => {
                while !r.is_empty() {
                    let name = r.name()?;
                    r.index()?; // Type index
                    obj.externals.push(External::Undefined { name, local: kind != EXTDEF });
                }
            }
            COMDEF | LCOMDEF => {
                while !r.is_empty() {
                    let name = r.name()?;
                    r.index()?; // Type index
                    let local = kind == LCOMDEF;
                    match r.u8()? {
                        0x61 => {
                            let count = r.communal_length()?;
                            let size = r.communal_length()?;
                            obj.externals.push(External::Communal {
                                name,
                                size: count * size,
                                local,
                            });
                        }
                        0x62 => {
                            let size = r.communal_length()?;
                            obj.externals.push(External::Communal { name, size, local });
                        }
                        segment @ 1..=0x5F => {
                            // Borland virtual segment, owned by the given SEGDEF
                            let size = r.communal_length()?;
                            obj.externals.push(External::Virtual(obj.virtuals.len()));
                            obj.virtuals.push(VirtualSegment {
                                name,
                                segment: segment as usize - 1,
                                data: vec![0; size as usize],
                                local,
                            });
                        }
                        data_type => bail!("Unsupported COMDEF data type {data_type:#x}"),
                    }
                }
            }
            PUBDEF | PUBDEF32 | LPUBDEF | LPUBDEF32 => {
                r.index()?; // Group index
                let segment = r.index()?;
                if segment == 0 {
                    // Absolute symbols are not supported
                    log::warn!("Skipping absolute OMF public symbols");
                    continue;
                }
                let segment = SegmentRef::from_index(segment)?;
                while !r.is_empty() {
                    let name = r.name()?;
                    let offset = r.word(is32)? as u64;
                    r.index()?; // Type index
                    let local = matches!(kind, LPUBDEF | LPUBDEF32);
                    obj.publics.push(Public { name, segment, offset, local });
                }
            }
            LEDATA | LEDATA32 => {
                let segment = SegmentRef::from_index(r.index()?)?;
                let offset = r.word(is32)? as u64;
                obj.write(segment, offset, r.rest())?;
                last_data = Some((segment, offset));
            }
            LIDATA | LIDATA32 => {
                let segment = SegmentRef::from_index(r.index()?)?;
                let offset = r.word(is32)? as u64;
                let mut expanded = Vec::new();
                while !r.is_empty() {
                    expand_iterated(&mut r, is32, &mut expanded)?;
                }
                obj.write(segment, offset, &expanded)?;
                last_data = Some((segment, offset));
            }
            FIXUPP | FIXUPP32 => {
                parse_fixups(&mut r, is32, last_data, &mut target_threads, &mut obj.fixups)?;
            }
            COMDAT | COMDAT32 => bail!("OMF COMDAT records are not supported"),
            MODEND | MODEND32 => break,
            _ => {}
        }
    }
    Ok(obj)
}

/// Expand one LIDATA iterated data block.
fn expand_iterated(r: &mut Reader, is32: bool, out: &mut Vec<u8>) -> Result<()> {
    let repeat = r.word(is32)?;
    let blocks = r.u16()?;
    if blocks == 0 {
        let len = r.u8()? as usize;
        let content = r.bytes(len)?;
        for _ in 0..repeat {
            out.extend_from_slice(content);
        }
    } else {
        let start = r.pos;
        for _ in 0..repeat {
            r.pos = start;
            for _ in 0..blocks {
                expand_iterated(r, is32, out)?;
            }
        }
    }
    Ok(())
}

fn parse_fixups(
    r: &mut Reader,
    is32: bool,
    last_data: Option<(SegmentRef, u64)>,
    target_threads: &mut [TargetThread; 4],
    out: &mut Vec<Fixup>,
) -> Result<()> {
    while !r.is_empty() {
        let first = r.u8()?;
        if first & 0x80 == 0 {
            // THREAD subrecord
            let method = (first >> 2) & 7;
            let thread = (first & 3) as usize;
            if first & 0x40 != 0 {
                // Frame thread: only methods F0-F2 have a datum
                if method < 3 {
                    r.index()?;
                }
            } else {
                let index = if method & 3 == 3 { r.u16()? } else { r.index()? };
                target_threads[thread] = TargetThread { method: method & 3, index };
            }
            continue;
        }
        let locat = ((first as u16) << 8) | r.u8()? as u16;
        let self_relative = locat & 0x4000 == 0;
        let location = ((locat >> 10) & 0xF) as u8;
        let record_offset = (locat & 0x3FF) as u64;
        let fix_data = r.u8()?;
        if fix_data & 0x80 == 0 && (fix_data >> 4) & 7 < 3 {
            r.index()?; // Frame datum
        }
        let has_displacement = fix_data & 0x04 == 0;
        let (method, index) = if fix_data & 0x08 != 0 {
            let thread = target_threads[(fix_data & 3) as usize];
            (thread.method, thread.index)
        } else {
            let method = fix_data & 3;
            (method, if method == 3 { r.u16()? } else { r.index()? })
        };
        let displacement = if has_displacement { r.word(is32)? as i32 as i64 } else { 0 };
        let target = match method {
            0 => FixupTarget::Segment(SegmentRef::from_index(index)?),
            1 => FixupTarget::Group(index as usize),
            2 => FixupTarget::External(index as usize),
            _ => FixupTarget::Frame,
        };
        let (segment, offset) = last_data.context("FIXUPP record without preceding data")?;
        out.push(Fixup {
            segment,
            offset: offset + record_offset,
            self_relative,
            location,
            target,
            displacement,
        });
    }
    Ok(())
}

fn segment_kind(segment: &Segment) -> SectionKind {
    let class = segment.class.to_ascii_uppercase();
    let name = segment.name.to_ascii_uppercase();
    if name.starts_with("$$") || class.starts_with("DEB") {
        // Borland ($$BSYMS, $$BTYPES, ...) debug information
        SectionKind::Unknown
    } else if class.contains("CODE") || class.ends_with("TEXT") {
        SectionKind::Code
    } else if class.contains("BSS") || class == "STACK" {
        SectionKind::Bss
    } else if class.contains("DATA") || class.contains("CONST") || class == "TLS" {
        SectionKind::Data
    } else {
        SectionKind::Unknown
    }
}

/// COFF name for well-known OMF segment names.
fn section_name(segment: &Segment) -> String {
    match segment.name.as_str() {
        "_TEXT" | "CODE" => ".text",
        "_DATA" | "DATA" => ".data",
        "_BSS" | "BSS" => ".bss",
        "_TLS" | "TLS" => ".tls",
        "CONST" => ".rdata",
        name => name,
    }
    .to_string()
}

/// Whether a Borland symbol names data rather than code: VMTs (`@TFoo@`), RTTI (`@$xp$4TFoo`),
/// variables, typed constants and resource strings (`_Name`), and literals (`@Unit@_123`).
pub fn is_borland_data_name(name: &str) -> bool {
    !name.starts_with('@')
        || name.ends_with('@')
        || name.starts_with("@$x")
        || is_borland_literal_name(name)
}

/// Compiler-generated Borland literal names, e.g. `@Unit@_16388`.
pub fn is_borland_literal_name(name: &str) -> bool {
    name.starts_with('@')
        && name
            .rsplit_once("@_")
            .is_some_and(|(_, id)| !id.is_empty() && id.bytes().all(|c| c.is_ascii_digit()))
}

/// Whether `data` begins (after an optional `int3` fill byte) with one of the thunks dcc32 writes
/// in front of a class's VMT for its interface methods: Self is adjusted from the interface
/// pointer to the object (`add eax, N` / `add dword [esp+4], N`), then the method is jumped to.
/// The block (thunks, interface method table and interface table) is code.
pub fn starts_with_interface_thunk(data: &[u8]) -> bool {
    let d = data.strip_prefix(&[0xCC]).unwrap_or(data);
    match d {
        // add eax, imm8 ; jmp rel32 | push eax; mov eax,[eax]; mov eax,[eax+..]
        [0x83, 0xC0, _, 0xE9, ..] | [0x83, 0xC0, _, 0x50, 0x8B, 0x00, 0x8B, ..] => true,
        // add dword [esp+4], imm8 ; jmp rel32 | mov eax,[esp+4]; mov eax,[eax]; jmp [eax+..]
        [0x83, 0x44, 0x24, 0x04, _, 0xE9, ..]
        | [0x83, 0x44, 0x24, 0x04, _, 0x8B, 0x44, 0x24, 0x04, 0x8B, 0x00, 0xFF, ..] => true,
        // add eax, imm32 / add dword [esp+4], imm32
        [0x05, _, _, _, _, 0xE9, ..] | [0x05, _, _, _, _, 0x50, 0x8B, 0x00, 0x8B, ..] => true,
        [0x81, 0x44, 0x24, 0x04, _, _, _, _, 0xE9, ..] => true,
        _ => false,
    }
}

/// Whether `data` begins with a stack frame prologue (`push ebp; mov ebp, esp`). An uncalled
/// `@Unit@_123` that does is a routine: the main block of a program (`begin .. end.`), which
/// nothing calls, or a nested routine only reached through its address.
pub fn starts_with_frame_prologue(data: &[u8]) -> bool { data.starts_with(&[0x55, 0x8B, 0xEC]) }

/// Name given to a Delphi unit's hidden initialization counter.
pub const INIT_COUNT_NAME: &str = "_InitCount";

/// Delphi gives every unit a counter in BSS that its initialization procedure
/// decrements first thing (`sub dword ptr [counter], 1`) and its finalization
/// increments. dcc32 emits no symbol for it, so references to it would land on
/// whatever variable precedes it. Find it through the INITDATA table entry that
/// points at the initialization procedure and name it [`INIT_COUNT_NAME`].
fn add_init_counter(obj: &mut OmfObject) {
    let is_class = |segment: SegmentRef, class: &str| match segment {
        SegmentRef::Segment(i) => {
            obj.segments.get(i).is_some_and(|s| s.class.eq_ignore_ascii_case(class))
        }
        SegmentRef::Virtual(_) => false,
    };
    let target_code = |target: FixupTarget| match target {
        FixupTarget::Segment(segment) => Some(segment),
        FixupTarget::External(i) => match obj.externals.get(i) {
            Some(External::Virtual(v)) => Some(SegmentRef::Virtual(*v)),
            _ => None,
        },
        _ => None,
    };
    let Some(init_proc) = obj
        .fixups
        .iter()
        .filter(|f| is_class(f.segment, "INITDATA"))
        .find_map(|f| target_code(f.target))
    else {
        return;
    };
    let data = match init_proc {
        SegmentRef::Segment(i) => &obj.segments[i].data,
        SegmentRef::Virtual(i) => &obj.virtuals[i].data,
    };
    let mut found = None;
    for pos in 0..data.len().min(64).saturating_sub(6) {
        if data[pos] != 0x83 || data[pos + 1] != 0x2D || data[pos + 6] != 1 {
            continue;
        }
        let Some(fixup) = obj
            .fixups
            .iter()
            .find(|f| f.segment == init_proc && f.offset == pos as u64 + 2 && !f.self_relative)
        else {
            continue;
        };
        let FixupTarget::Segment(bss) = fixup.target else { continue };
        if !is_class(bss, "BSS") {
            continue;
        }
        let stored = u32::from_le_bytes(data[pos + 2..pos + 6].try_into().unwrap()) as i64;
        found = Some((bss, (stored + fixup.displacement) as u64));
        break;
    }
    let Some((segment, offset)) = found else { return };
    if obj.publics.iter().any(|p| p.segment == segment && p.offset == offset) {
        return;
    }
    obj.publics.push(Public { name: INIT_COUNT_NAME.to_string(), segment, offset, local: true });
}

/// Where a segment or virtual segment lands in the output sections.
#[derive(Copy, Clone)]
struct Placement {
    section: usize,
    offset: u64,
}

struct PendingSymbol {
    symbol: Symbol,
    /// Section symbols are sorted first within their section
    is_section: bool,
}

pub fn parse(data: &[u8], config: &DiffObjConfig) -> Result<(ArchX86, Vec<Section>, Vec<Symbol>)> {
    let mut obj = parse_records(data)?;
    add_init_counter(&mut obj);

    // Plan the output sections
    let mut sections = Vec::<Section>::new();
    let mut section_ids = BTreeMap::<String, usize>::new();
    let mut add_section = |sections: &mut Vec<Section>, name: String, kind, align: u64| {
        let unique_id = section_ids.entry(name.clone()).or_insert(0);
        let id = format!("{name}-{unique_id}");
        *unique_id += 1;
        sections.push(Section {
            id,
            name,
            kind,
            align: NonZeroU64::new(align),
            ..Default::default()
        });
        sections.len() - 1
    };
    let mut segment_sections = Vec::<Option<usize>>::with_capacity(obj.segments.len());
    for segment in &obj.segments {
        let kind = segment_kind(segment);
        segment_sections.push(if kind == SectionKind::Unknown {
            None
        } else {
            Some(add_section(&mut sections, section_name(segment), kind, segment.align))
        });
    }
    let mut rdata_section = None;
    let mut rdata = |sections: &mut Vec<Section>| {
        *rdata_section
            .get_or_insert_with(|| add_section(sections, RDATA.to_string(), SectionKind::Data, 4))
    };

    // A code segment whose public symbols are all data (Delphi keeps RTTI there) goes to .rdata
    let mut placements = BTreeMap::<SegmentRef, Placement>::new();
    let mut place =
        |sections: &mut [Section], section: usize, segment: SegmentRef, len: u64, align: u64| {
            let target = &mut sections[section];
            let offset = target.size.next_multiple_of(align.max(1));
            target.size = offset + len;
            placements.insert(segment, Placement { section, offset });
        };
    // dcc32 names literals and nested / implementation-only routines alike (`@Unit@_123`);
    // a routine is the target of a call or jump (a self-relative fixup).
    let called_virtuals: BTreeSet<usize> = obj
        .fixups
        .iter()
        .filter(|f| f.self_relative)
        .filter_map(|f| match f.target {
            FixupTarget::External(e) => match obj.externals.get(e) {
                Some(External::Virtual(v)) => Some(*v),
                _ => None,
            },
            FixupTarget::Segment(SegmentRef::Virtual(v)) => Some(v),
            _ => None,
        })
        .collect();
    let is_routine = |i: usize| {
        called_virtuals.contains(&i)
            || (is_borland_literal_name(&obj.virtuals[i].name)
                && (starts_with_interface_thunk(&obj.virtuals[i].data)
                    || starts_with_frame_prologue(&obj.virtuals[i].data)))
    };
    for (i, segment) in obj.segments.iter().enumerate() {
        let Some(mut section) = segment_sections[i] else { continue };
        if sections[section].kind == SectionKind::Code && segment.length > 0 {
            let mut publics =
                obj.publics.iter().filter(|p| p.segment == SegmentRef::Segment(i)).peekable();
            if publics.peek().is_some() && publics.all(|p| is_borland_data_name(&p.name)) {
                section = rdata(&mut sections);
            }
        }
        place(&mut sections, section, SegmentRef::Segment(i), segment.length, segment.align);
    }
    for (i, virt) in obj.virtuals.iter().enumerate() {
        let segment = obj.segments.get(virt.segment).context("Invalid virtual segment owner")?;
        let Some(mut section) = segment_sections[virt.segment] else { continue };
        // stdcall / safecall / pascal routines have no leading `@` (`Name`, `TFoo@Name`);
        // in a code segment only resource strings (`__S`) and cdecl-like `_Name` stay ambiguous.
        let plain_routine = !virt.name.starts_with('@') && !virt.name.starts_with("__");
        if sections[section].kind == SectionKind::Code
            && is_borland_data_name(&virt.name)
            && !is_routine(i)
            && !plain_routine
        {
            section = rdata(&mut sections);
        }
        place(
            &mut sections,
            section,
            SegmentRef::Virtual(i),
            virt.data.len() as u64,
            segment.align,
        );
    }

    // Copy the data
    for section in sections.iter_mut().filter(|s| s.kind != SectionKind::Bss) {
        section.data = SectionData(vec![0; section.size as usize]);
    }
    for (&segment, placement) in &placements {
        let section = &mut sections[placement.section];
        if section.kind == SectionKind::Bss {
            continue;
        }
        let bytes = match segment {
            SegmentRef::Segment(i) => &obj.segments[i].data,
            SegmentRef::Virtual(i) => &obj.virtuals[i].data,
        };
        let start = placement.offset as usize;
        let len = bytes.len().min(section.data.len().saturating_sub(start));
        section.data.0[start..start + len].copy_from_slice(&bytes[..len]);
    }

    // Symbols
    let mut pending = Vec::<PendingSymbol>::new();
    let make_symbol = |name: String, kind, section, address, size, flags: SymbolFlagSet| {
        let demangled_name = config.demangler.demangle(&name);
        let normalized_name = super::read::get_normalized_symbol_name(&name);
        let mut flags = flags;
        if is_borland_literal_name(&name) && kind != SymbolKind::Function {
            flags |= SymbolFlag::CompilerGenerated;
        }
        Symbol {
            name,
            demangled_name,
            normalized_name,
            address,
            size,
            kind,
            section,
            flags,
            align: None,
            virtual_address: None,
        }
    };
    let visibility = |local: bool| -> SymbolFlagSet {
        if local { SymbolFlag::Local.into() } else { SymbolFlag::Global.into() }
    };
    let section_symbol_kind = |section: usize| match sections[section].kind {
        SectionKind::Code => SymbolKind::Function,
        _ => SymbolKind::Object,
    };
    for (i, section) in sections.iter().enumerate() {
        pending.push(PendingSymbol {
            symbol: make_symbol(
                format!("[{}]", section.name),
                SymbolKind::Section,
                Some(i),
                0,
                0,
                SymbolFlag::Local.into(),
            ),
            is_section: true,
        });
    }
    for (i, virt) in obj.virtuals.iter().enumerate() {
        let Some(placement) = placements.get(&SegmentRef::Virtual(i)) else { continue };
        let local = virt.local || is_borland_literal_name(&virt.name);
        pending.push(PendingSymbol {
            symbol: make_symbol(
                virt.name.clone(),
                section_symbol_kind(placement.section),
                Some(placement.section),
                placement.offset,
                virt.data.len() as u64,
                visibility(local),
            ),
            is_section: false,
        });
    }
    for public in &obj.publics {
        let Some(placement) = placements.get(&public.segment) else { continue };
        // Size up to the next public symbol or the end of the segment
        let end = obj
            .publics
            .iter()
            .filter(|p| p.segment == public.segment && p.offset > public.offset)
            .map(|p| p.offset)
            .min()
            .unwrap_or(match public.segment {
                SegmentRef::Segment(i) => obj.segments[i].length,
                SegmentRef::Virtual(i) => obj.virtuals[i].data.len() as u64,
            });
        pending.push(PendingSymbol {
            symbol: make_symbol(
                public.name.clone(),
                section_symbol_kind(placement.section),
                Some(placement.section),
                placement.offset + public.offset,
                end.saturating_sub(public.offset),
                visibility(public.local),
            ),
            is_section: false,
        });
    }
    // Sort defined symbols by section, then address (section symbols first), then size
    pending.sort_by(|a, b| {
        a.symbol
            .section
            .cmp(&b.symbol.section)
            .then_with(|| b.is_section.cmp(&a.is_section))
            .then_with(|| a.symbol.address.cmp(&b.symbol.address))
            .then_with(|| a.symbol.size.cmp(&b.symbol.size))
    });
    let mut symbols = pending.into_iter().map(|p| p.symbol).collect::<Vec<_>>();
    let section_symbols = (0..sections.len())
        .map(|i| symbols.iter().position(|s| s.kind == SymbolKind::Section && s.section == Some(i)))
        .collect::<Vec<_>>();
    let mut virtual_symbols = vec![None; obj.virtuals.len()];
    for (i, virt) in obj.virtuals.iter().enumerate() {
        if let Some(placement) = placements.get(&SegmentRef::Virtual(i)) {
            virtual_symbols[i] = symbols.iter().position(|s| {
                s.section == Some(placement.section)
                    && s.address == placement.offset
                    && s.name == virt.name
            });
        }
    }
    // External symbols last
    let mut external_symbols = Vec::<Option<usize>>::with_capacity(obj.externals.len());
    for external in &obj.externals {
        external_symbols.push(match external {
            External::Virtual(i) => virtual_symbols[*i],
            External::Undefined { name, local } => {
                symbols.push(make_symbol(
                    name.clone(),
                    SymbolKind::Unknown,
                    None,
                    0,
                    0,
                    visibility(*local),
                ));
                Some(symbols.len() - 1)
            }
            External::Communal { name, size, local } => {
                symbols.push(make_symbol(
                    name.clone(),
                    SymbolKind::Object,
                    None,
                    0,
                    *size,
                    visibility(*local) | SymbolFlag::Common,
                ));
                Some(symbols.len() - 1)
            }
        });
    }

    // Relocations
    for fixup in &obj.fixups {
        let Some(location) = placements.get(&fixup.segment) else { continue };
        let section_kind = sections[location.section].kind;
        if section_kind == SectionKind::Bss {
            continue;
        }
        let (size, typ) = match (fixup.location, fixup.self_relative) {
            (9 | 13, false) => (4, pe::IMAGE_REL_I386_DIR32),
            (9 | 13, true) => (4, pe::IMAGE_REL_I386_REL32),
            (1 | 5, false) => (2, pe::IMAGE_REL_I386_DIR16),
            (1 | 5, true) => (2, pe::IMAGE_REL_I386_REL16),
            (location, _) => {
                log::warn!("Skipping unsupported OMF fixup location type {location}");
                continue;
            }
        };
        let address = location.offset + fixup.offset;
        let data = &mut sections[location.section].data.0;
        let field = data
            .get_mut(address as usize..address as usize + size)
            .ok_or_else(|| anyhow!("OMF fixup at {address:#x} out of bounds"))?;
        let stored = if size == 4 {
            i32::from_le_bytes(field.try_into()?) as i64
        } else {
            i16::from_le_bytes(field.try_into()?) as i64
        };
        let addend = stored + fixup.displacement;
        let (target_symbol, addend) = match fixup.target {
            FixupTarget::External(index) => {
                let symbol = index
                    .checked_sub(1)
                    .and_then(|i| external_symbols.get(i).copied().flatten())
                    .ok_or_else(|| anyhow!("Invalid OMF external index {index}"))?;
                (symbol, addend)
            }
            FixupTarget::Segment(segment) => {
                let Some(target) = placements.get(&segment) else { continue };
                let address = target.offset.wrapping_add_signed(addend);
                match best_symbol(&symbols, target.section, address) {
                    Some(i) => (i, address.wrapping_sub(symbols[i].address) as i64),
                    None => match symbol_just_after(&symbols, target.section, address) {
                        // `Arr[I]` of an array indexed from 1 refers to `_Arr - 4`: keep the
                        // symbol and a negative addend, like the delinked target does
                        Some(i) => (i, address.wrapping_sub(symbols[i].address) as i64),
                        None => match section_symbols[target.section] {
                            Some(i) => (i, address as i64),
                            None => continue,
                        },
                    },
                }
            }
            FixupTarget::Group(group) => {
                log::warn!(
                    "Skipping OMF fixup against group {group} ({} segments)",
                    obj.groups.get(group.wrapping_sub(1)).map_or(0, Vec::len)
                );
                continue;
            }
            FixupTarget::Frame => {
                log::warn!("Skipping OMF fixup against a frame number");
                continue;
            }
        };
        // Store the symbol-relative addend in the data, like COFF
        if size == 4 {
            field.copy_from_slice(&(addend as i32).to_le_bytes());
        } else {
            field.copy_from_slice(&(addend as i16).to_le_bytes());
        }
        sections[location.section].relocations.push(Relocation {
            flags: RelocationFlags::Coff(typ),
            address,
            target_symbol,
            addend,
        });
    }
    for section in &mut sections {
        section.relocations.sort_by_key(|r| r.address);
    }

    Ok((ArchX86::new_i386(), sections, symbols))
}

/// The symbol in `section` that contains `address`, preferring the closest one.
fn best_symbol(symbols: &[Symbol], section: usize, address: u64) -> Option<usize> {
    symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| {
            s.section == Some(section)
                && s.kind != SymbolKind::Section
                && s.address <= address
                && (s.size == 0 || address < s.address + s.size)
        })
        .max_by_key(|(_, s)| s.address)
        .map(|(i, _)| i)
}

/// The closest symbol of `section` that starts at most [`SYMBOL_REACH_BEFORE`] bytes after `address`
/// (`address` may have wrapped below zero).
fn symbol_just_after(symbols: &[Symbol], section: usize, address: u64) -> Option<usize> {
    symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| {
            s.section == Some(section)
                && s.kind != SymbolKind::Section
                && s.address.wrapping_sub(address) as i64 > 0
                && s.address.wrapping_sub(address) <= SYMBOL_REACH_BEFORE
        })
        .min_by_key(|(_, s)| s.address)
        .map(|(i, _)| i)
}

/// How far in front of a data symbol a relocation may point and still count as
/// `symbol - n`.
const SYMBOL_REACH_BEFORE: u64 = 16;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn data_names() {
        assert!(is_borland_data_name("@TProbe@"));
        assert!(is_borland_data_name("@Probe@TProbe@"));
        assert!(is_borland_data_name("@$xp$6TProbe"));
        assert!(is_borland_data_name("_GTable"));
        assert!(is_borland_data_name("__SHello"));
        assert!(is_borland_data_name("@Probe@_16388"));
        assert!(!is_borland_data_name("@TProbe@Twice$qqri"));
        assert!(!is_borland_data_name("@TProbe@$bctr"));
        assert!(!is_borland_data_name("@AddOne"));
        assert!(!is_borland_data_name("@Probe@initialization$qqrv"));
    }

    #[test]
    fn detect() {
        assert!(is_omf(b"\x80\x0b\x00\x09Probe.pas\x00"));
        assert!(!is_omf(b"\x80\x0b\x00\x08Probe.pas\x00"));
        assert!(!is_omf(b"\x4c\x01\x00\x00\x00"));
    }
}
