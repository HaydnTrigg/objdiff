//! Logical function diff (`functionRelocDiffs.logical`).
//!
//! Two aligned rows match when they do the same thing, even if they are written differently:
//!
//! - Registers are compared by where their value comes from, not by name. Every register read
//!   must get its value from the same row on both sides (or, at function entry, from the same
//!   argument register; entry values of callee-saved registers are interchangeable). So a
//!   function that keeps a value in esi where the other keeps it in ebx matches, and so do
//!   different choices for different live ranges.
//! - At a call, argument registers loaded since the previous call and not read since must come
//!   from the same row on both sides (a swapped `mov eax, A` / `mov edx, B` is a real
//!   difference). The same goes for the return register at a return.
//! - Short runs of instructions that do not depend on each other may be in a different order.
//!
//! Register values are tracked in instruction order without following branches, which is
//! enough because both sides have the same shape wherever this matters.

use alloc::{collections::BTreeMap, vec, vec::Vec};
use core::ops::Range;

use anyhow::{Context, Result};

use super::{
    DiffObjConfig, InstructionDiffKind, InstructionDiffRow,
    code::{PENALTY_REG_DIFF, reloc_eq},
};
use crate::{
    arch::{LogicalAbi, LogicalFlow, LogicalFlowKind},
    obj::{InstructionArg, Object, ParsedInstruction, ResolvedInstructionRef},
};

/// Longest run of instructions that may be reordered.
const MAX_WINDOW: usize = 4;

struct Ins<'a> {
    resolved: ResolvedInstructionRef<'a>,
    parsed: ParsedInstruction,
    flow: LogicalFlow,
}

fn load<'a>(
    obj: &'a Object,
    symbol_idx: usize,
    rows: &[InstructionDiffRow],
    diff_config: &DiffObjConfig,
) -> Result<Vec<Option<Ins<'a>>>> {
    rows.iter()
        .map(|row| {
            let Some(ins_ref) = row.ins_ref else { return Ok(None) };
            let resolved = obj
                .resolve_instruction_ref(symbol_idx, ins_ref)
                .context("Failed to resolve instruction")?;
            let parsed = obj.arch.process_instruction(resolved, diff_config)?;
            let flow = obj.arch.logical_flow(resolved, diff_config)?;
            Ok(Some(Ins { resolved, parsed, flow }))
        })
        .collect()
}

/// Where a register's value comes from: the routine's caller, or the row (left-side index)
/// that wrote it.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Origin {
    Entry,
    Row(usize),
}

#[derive(Debug, Copy, Clone)]
struct Def {
    origin: Origin,
    /// Read since it was written
    consumed: bool,
}

const ENTRY: Def = Def { origin: Origin::Entry, consumed: false };

#[derive(Default)]
struct Registers {
    defs: BTreeMap<u8, Def>,
    last_call: Option<usize>,
}

impl Registers {
    fn def(&self, family: u8) -> Def { self.defs.get(&family).copied().unwrap_or(ENTRY) }

    /// The value in `family` if it was loaded since the last call and not read yet: a likely
    /// call argument or return value.
    fn pending(&self, family: u8) -> Option<usize> {
        match self.def(family) {
            Def { origin: Origin::Row(row), consumed: false }
                if self.last_call.is_none_or(|call| row > call) =>
            {
                Some(row)
            }
            _ => None,
        }
    }

    fn apply(&mut self, row: usize, flow: &LogicalFlow, abi: &LogicalAbi) {
        for read in &flow.reads {
            self.defs.entry(read.family).or_insert(ENTRY).consumed = true;
        }
        match flow.kind {
            LogicalFlowKind::Call => {
                for &family in abi.call_registers {
                    self.defs.insert(family, Def { origin: Origin::Row(row), consumed: false });
                }
                self.last_call = Some(row);
            }
            LogicalFlowKind::Return => self.last_call = Some(row),
            LogicalFlowKind::Normal | LogicalFlowKind::Branch => {}
        }
        for write in &flow.writes {
            self.defs.insert(write.family, Def { origin: Origin::Row(row), consumed: false });
        }
    }
}

struct Logic<'a> {
    left_obj: &'a Object,
    right_obj: &'a Object,
    left: Vec<Option<Ins<'a>>>,
    right: Vec<Option<Ins<'a>>>,
    left_rows: &'a [InstructionDiffRow],
    right_rows: &'a [InstructionDiffRow],
    abi: LogicalAbi,
    diff_config: &'a DiffObjConfig,
}

impl Logic<'_> {
    /// Left row `i` and right row `j` are the same instruction up to register names.
    /// `left_of` maps right rows to the left rows they are paired with (for branch targets).
    fn args_equal(&self, i: usize, j: usize, left_of: &[usize]) -> bool {
        let (Some(l), Some(r)) = (&self.left[i], &self.right[j]) else { return false };
        if l.resolved.ins_ref.opcode != r.resolved.ins_ref.opcode
            || l.parsed.mnemonic != r.parsed.mnemonic
            || l.parsed.args.len() != r.parsed.args.len()
        {
            return false;
        }
        if l.resolved.code == r.resolved.code
            && reloc_eq(self.left_obj, self.right_obj, l.resolved, r.resolved, self.diff_config)
        {
            // Same bytes: equal as in the strict diff (registers are still checked by flow)
            return true;
        }
        let relax = self.diff_config.relax_reloc_diffs();
        l.parsed.args.iter().zip(&r.parsed.args).all(|(a, b)| match (a, b) {
            (InstructionArg::Value(x), InstructionArg::Value(y)) => {
                x.loose_eq(y)
                    || match (
                        self.left_obj.arch.logical_register(a),
                        self.right_obj.arch.logical_register(b),
                    ) {
                        // Which register is checked by where its value comes from
                        (Some(ra), Some(rb)) => ra.part == rb.part,
                        _ => false,
                    }
            }
            (InstructionArg::Reloc, InstructionArg::Reloc) => {
                reloc_eq(self.left_obj, self.right_obj, l.resolved, r.resolved, self.diff_config)
            }
            (InstructionArg::BranchDest(_), InstructionArg::BranchDest(_)) => {
                let left_target = self.left_rows[i].branch_to.as_ref().map(|b| b.ins_idx as usize);
                let right_target = self.right_rows[j]
                    .branch_to
                    .as_ref()
                    .and_then(|b| left_of.get(b.ins_idx as usize).copied());
                left_target == right_target
            }
            (InstructionArg::Value(_) | InstructionArg::BranchDest(_), InstructionArg::Reloc) => {
                relax
            }
            _ => false,
        })
    }

    fn origin_eq(&self, l: Origin, r: Origin, l_family: u8, r_family: u8) -> bool {
        match (l, r) {
            (Origin::Row(a), Origin::Row(b)) => a == b,
            (Origin::Entry, Origin::Entry) => {
                l_family == r_family
                    || (self.abi.callee_saved.contains(&l_family)
                        && self.abi.callee_saved.contains(&r_family))
            }
            _ => false,
        }
    }

    /// Both instructions read values from the same places.
    fn flow_equal(&self, l: &LogicalFlow, r: &LogicalFlow, ls: &Registers, rs: &Registers) -> bool {
        if l.kind != r.kind || l.reads.len() != r.reads.len() {
            return false;
        }
        let reads_ok = l.reads.iter().zip(&r.reads).all(|(a, b)| {
            a.part == b.part
                && self.origin_eq(
                    ls.def(a.family).origin,
                    rs.def(b.family).origin,
                    a.family,
                    b.family,
                )
        });
        if !reads_ok {
            return false;
        }
        let boundary: &[u8] = match l.kind {
            LogicalFlowKind::Call => self.abi.call_registers,
            LogicalFlowKind::Return => self.abi.return_registers,
            LogicalFlowKind::Normal | LogicalFlowKind::Branch => &[],
        };
        boundary.iter().all(|&family| {
            let (pl, pr) = (ls.pending(family), rs.pending(family));
            pl.is_none() && pr.is_none() || pl == pr
        })
    }

    /// Walk the rows in left order with right row `partner[i]` against left row `i`; returns
    /// which left rows match.
    fn simulate(&self, partner: &[usize], left_of: &[usize]) -> Vec<bool> {
        let mut ls = Registers::default();
        let mut rs = Registers::default();
        let mut equal = vec![false; partner.len()];
        for (i, &j) in partner.iter().enumerate() {
            let (l, r) = (&self.left[i], &self.right[j]);
            if let (Some(l), Some(r)) = (l, r) {
                equal[i] =
                    self.args_equal(i, j, left_of) && self.flow_equal(&l.flow, &r.flow, &ls, &rs);
            }
            if let Some(l) = l {
                ls.apply(i, &l.flow, &self.abi);
            }
            if let Some(r) = r {
                rs.apply(i, &r.flow, &self.abi);
            }
        }
        equal
    }

    /// The instructions of one side in `range` can run in any order.
    fn independent(&self, side: &[Option<Ins>], range: Range<usize>) -> bool {
        let flows = range.filter_map(|t| side[t].as_ref().map(|ins| &ins.flow)).collect::<Vec<_>>();
        flows.iter().enumerate().all(|(x, fx)| {
            fx.kind == LogicalFlowKind::Normal
                && flows.iter().enumerate().all(|(y, fy)| {
                    x == y
                        || !(fx.writes.iter().any(|w| {
                            fy.reads.iter().chain(&fy.writes).any(|o| o.family == w.family)
                        }) || fx.writes_memory && (fy.reads_memory || fy.writes_memory)
                            || fx.writes_flags && (fy.reads_flags || fy.writes_flags))
                })
        })
    }

    /// Runs of rows that line up only when the right side is reordered, with the order.
    fn find_windows(&self) -> Vec<(Range<usize>, Vec<usize>)> {
        let n = self.left.len();
        let identity = (0..n).collect::<Vec<_>>();
        let mut windows = Vec::new();
        let mut i = 0;
        while i < n {
            let start_ok = self.left_rows[i].kind != InstructionDiffKind::None
                && self.left[i].is_some()
                && self.right[i].is_some()
                && !self.args_equal(i, i, &identity);
            if !start_ok {
                i += 1;
                continue;
            }
            let mut found = None;
            for len in 2..=MAX_WINDOW.min(n - i) {
                let range = i..i + len;
                // Every row present on both sides, nothing branches into the middle
                if range.clone().any(|t| self.left[t].is_none() || self.right[t].is_none())
                    || (i + 1..i + len).any(|t| {
                        self.left_rows[t].branch_from.is_some()
                            || self.right_rows[t].branch_from.is_some()
                    })
                {
                    break;
                }
                let Some(order) = self.permutation(range.clone(), &identity) else { continue };
                if self.independent(&self.left, range.clone())
                    && self.independent(&self.right, range.clone())
                {
                    found = Some((range, order));
                    break;
                }
            }
            match found {
                Some((range, order)) => {
                    i = range.end;
                    windows.push((range, order));
                }
                None => i += 1,
            }
        }
        windows
    }

    /// A pairing of the left rows in `range` with the right rows in `range` (right row for
    /// each left row) under which each pair is the same instruction.
    fn permutation(&self, range: Range<usize>, identity: &[usize]) -> Option<Vec<usize>> {
        fn search(
            ctx: &Logic,
            range: &Range<usize>,
            identity: &[usize],
            order: &mut Vec<usize>,
            used: &mut Vec<bool>,
        ) -> bool {
            let i = range.start + order.len();
            if i == range.end {
                return true;
            }
            for (k, j) in range.clone().enumerate() {
                if used[k] || !ctx.args_equal(i, j, identity) {
                    continue;
                }
                used[k] = true;
                order.push(j);
                if search(ctx, range, identity, order, used) {
                    return true;
                }
                order.pop();
                used[k] = false;
            }
            false
        }
        let mut order = Vec::with_capacity(range.len());
        let mut used = vec![false; range.len()];
        search(self, &range, identity, &mut order, &mut used).then_some(order)
    }
}

/// Rework the strict diff of a function into the logical one. `row_penalty` holds the strict
/// score of each row. Returns the new score, or None when the architecture has no logical diff.
pub(crate) fn logical_diff(
    left_obj: &Object,
    right_obj: &Object,
    left_symbol_idx: usize,
    right_symbol_idx: usize,
    left_rows: &mut [InstructionDiffRow],
    right_rows: &mut [InstructionDiffRow],
    row_penalty: &[u64],
    diff_config: &DiffObjConfig,
) -> Result<Option<u64>> {
    let (Some(abi), Some(_)) = (left_obj.arch.logical_abi(), right_obj.arch.logical_abi()) else {
        return Ok(None);
    };
    let n = left_rows.len();
    let (equal, partner) = {
        let ctx = Logic {
            left_obj,
            right_obj,
            left: load(left_obj, left_symbol_idx, left_rows, diff_config)?,
            right: load(right_obj, right_symbol_idx, right_rows, diff_config)?,
            left_rows,
            right_rows,
            abi,
            diff_config,
        };
        let mut windows = ctx.find_windows();
        loop {
            let mut partner = (0..n).collect::<Vec<_>>();
            for (range, order) in &windows {
                for (i, &j) in range.clone().zip(order) {
                    partner[i] = j;
                }
            }
            let mut left_of = vec![0; n];
            for (i, &j) in partner.iter().enumerate() {
                left_of[j] = i;
            }
            let equal = ctx.simulate(&partner, &left_of);
            // A reordering only stands if it makes the whole run match
            let before = windows.len();
            windows.retain(|(range, _)| range.clone().all(|i| equal[i]));
            if windows.len() == before {
                break (equal, partner);
            }
        }
    };

    let mut score = 0;
    for (i, &j) in partner.iter().enumerate() {
        if equal[i] {
            for row in [&mut left_rows[i], &mut right_rows[j]] {
                row.kind = InstructionDiffKind::None;
                row.arg_diff.clear();
            }
        } else if left_rows[i].kind == InstructionDiffKind::None
            && left_rows[i].ins_ref.is_some()
            && right_rows[j].ins_ref.is_some()
        {
            // Same text, but a register holds a different value
            left_rows[i].kind = InstructionDiffKind::ArgMismatch;
            right_rows[j].kind = InstructionDiffKind::ArgMismatch;
            score += PENALTY_REG_DIFF;
        } else {
            score += row_penalty[i];
        }
    }
    Ok(Some(score))
}
