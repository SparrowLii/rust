//! Structurally proves MIR prerequisites for the local LLVM loop preload pass.

use rustc_abi::Endian;
use rustc_data_structures::fx::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};

use crate::ssa::SsaLocals;

pub(super) struct LoopPreloadMarker;

#[derive(Clone, Copy)]
struct Definition<'a, 'tcx> {
    rvalue: &'a Rvalue<'tcx>,
    location: Location,
}

#[derive(Debug)]
#[allow(dead_code)]
struct MirLoopPreloadProof {
    input: Local,
    position: Local,
    tag: Local,
    tag_type: Local,
    entry: Local,
    loaded: Local,
    next_position: Local,
    header: BasicBlock,
    latch: BasicBlock,
}

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ssa: SsaLocals,
    definitions: IndexVec<Local, Option<Definition<'a, 'tcx>>>,
    dominators: rustc_data_structures::graph::dominators::Dominators<BasicBlock>,
}

impl<'a, 'tcx> Analyzer<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        let typing_env = body.typing_env(tcx);
        let ssa = SsaLocals::new(tcx, body, typing_env);
        let mut definitions = IndexVec::from_elem_n(None, body.local_decls.len());
        let mut assignment_counts = IndexVec::from_elem_n(0, body.local_decls.len());
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let Some((place, rvalue)) = statement.kind.as_assign() else { continue };
                let Some(local) = place.as_local() else { continue };
                assignment_counts[local] += 1;
                if assignment_counts[local] == 1 {
                    definitions[local] = Some(Definition {
                        rvalue,
                        location: Location { block: bb, statement_index },
                    });
                } else {
                    definitions[local] = None;
                }
            }
        }
        Self {
            tcx,
            body,
            typing_env,
            ssa,
            definitions,
            dominators: body.basic_blocks.dominators().clone(),
        }
    }

    fn canonical(&self, local: Local) -> Local {
        self.ssa.copy_classes()[local]
    }

    fn operand_local(&self, operand: &Operand<'tcx>) -> Option<Local> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => place.as_local(),
            Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
        }
    }

    fn same_operand_local(&self, operand: &Operand<'tcx>, local: Local) -> bool {
        self.operand_local(operand).is_some_and(|other| self.canonical(other) == self.canonical(local))
    }

    fn integer_constant(&self, operand: &Operand<'tcx>) -> Option<u128> {
        let constant = operand.constant()?;
        let scalar = constant.const_.try_eval_scalar_int(self.tcx, self.typing_env)?;
        Some(scalar.to_uint(scalar.size()))
    }

    fn binary_definition(&self, local: Local, op: BinOp) -> Option<(&Operand<'tcx>, &Operand<'tcx>)> {
        let definition = self.definitions[local]?;
        let Rvalue::BinaryOp(actual, operands) = definition.rvalue else { return None };
        (*actual == op).then_some((&operands.0, &operands.1))
    }

    fn binary_operands(&self, local: Local, op: BinOp) -> Option<(&Operand<'tcx>, &Operand<'tcx>)> {
        if let Some(result) = self.binary_definition(local, op) {
            return Some(result);
        }
        let definition = self.definitions[local]?;
        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) = definition.rvalue else {
            return None;
        };
        let [ProjectionElem::Field(field, _)] = place.projection.as_ref() else { return None };
        if field.as_usize() != 0 {
            return None;
        }
        let parent = self.definitions[place.local]?;
        let Rvalue::BinaryOp(actual, operands) = parent.rvalue else { return None };
        (*actual == op).then_some((&operands.0, &operands.1))
    }

    fn add_operands(&self, local: Local) -> Option<(&Operand<'tcx>, &Operand<'tcx>)> {
        if let Some(result) = self.binary_operands(local, BinOp::Add) {
            return Some(result);
        }
        let definition = self.definitions[local]?;
        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) = definition.rvalue else {
            return None;
        };
        let [ProjectionElem::Field(field, _)] = place.projection.as_ref() else { return None };
        if field.as_usize() != 0 {
            return None;
        }
        let parent = self.definitions[place.local]?;
        let Rvalue::BinaryOp(BinOp::AddWithOverflow, operands) = parent.rvalue else { return None };
        Some((&operands.0, &operands.1))
    }

    fn cast_source(&self, local: Local) -> Option<Local> {
        let definition = self.definitions[local]?;
        match definition.rvalue {
            Rvalue::Cast(_, operand, _) | Rvalue::Use(operand, _) => self.operand_local(operand),
            _ => None,
        }
    }

    fn peel_copy_cast(&self, mut local: Local) -> Local {
        for _ in 0..8 {
            let Some(source) = self.cast_source(local) else { break };
            if source == local {
                break;
            }
            local = source;
        }
        local
    }

    fn same_value(&self, left: Local, right: Local) -> bool {
        let left = self.peel_copy_cast(left);
        let right = self.peel_copy_cast(right);
        self.canonical(left) == self.canonical(right)
    }

    fn equivalent_through_cast(&self, local: Local, expected: Local) -> bool {
        self.same_value(local, expected)
    }

    fn find_tag_type(&self, tag: Local) -> Option<Local> {
        self.definitions.indices().find(|&local| {
            let Some((left, right)) = self.binary_operands(local, BinOp::BitAnd) else {
                return false;
            };
            (self.same_operand_local(left, tag) && self.integer_constant(right) == Some(3))
                || (self.same_operand_local(right, tag) && self.integer_constant(left) == Some(3))
        })
    }

    fn find_step(&self, tag_type: Local) -> Option<Local> {
        self.definitions.indices().find(|&local| {
            let Some((left, right)) = self.add_operands(local) else {
                return false;
            };
            let left_tag = self.operand_local(left).is_some_and(|value| {
                self.equivalent_through_cast(value, tag_type)
            });
            let right_tag = self.operand_local(right).is_some_and(|value| {
                self.equivalent_through_cast(value, tag_type)
            });
            (left_tag && self.integer_constant(right) == Some(1))
                || (right_tag && self.integer_constant(left) == Some(1))
        })
    }

    fn find_position_update(&self, tag_type: Local) -> Option<(Local, Local)> {
        let step = self.find_step(tag_type)?;
        let mut result = None;
        for data in self.body.basic_blocks.iter() {
            for statement in &data.statements {
                let Some((destination, rvalue)) = statement.kind.as_assign() else { continue };
                let Some(next_position) = destination.as_local() else { continue };
                let Rvalue::BinaryOp(BinOp::Add, operands) = rvalue else { continue };
                let Some(left_local) = self.operand_local(&operands.0) else { continue };
                let Some(right_local) = self.operand_local(&operands.1) else { continue };
                if self.equivalent_through_cast(left_local, step) {
                    result = Some((right_local, next_position));
                } else if self.equivalent_through_cast(right_local, step) {
                    result = Some((left_local, next_position));
                }
            }
        }
        result
    }

    fn slice_tag(&self, local: Local) -> Option<(Local, Local)> {
        let definition = self.definitions[local]?;
        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) = definition.rvalue else {
            return None;
        };
        let [ProjectionElem::Deref, ProjectionElem::Index(position)] = place.projection.as_ref() else {
            return None;
        };
        let input = place.local;
        let ty::Ref(_, pointee, mutability) = self.body.local_decls[input].ty.kind() else {
            return None;
        };
        if *mutability != Mutability::Not || !matches!(pointee.kind(), ty::Slice(element) if *element == self.tcx.types.u8)
        {
            return None;
        }
        Some((input, *position))
    }

    fn pointer_offset(&self, local: Local) -> Option<(Local, Local)> {
        let definition = self.definitions[local]?;
        let Rvalue::BinaryOp(BinOp::Offset, operands) = definition.rvalue else { return None };
        Some((self.operand_local(&operands.0)?, self.operand_local(&operands.1)?))
    }

    fn raw_tag(&self, local: Local) -> Option<(Local, Local)> {
        let definition = self.definitions[local]?;
        let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) = definition.rvalue else {
            return None;
        };
        let [ProjectionElem::Deref] = place.projection.as_ref() else { return None };
        let (input, position) = self.pointer_offset(place.local)?;
        let ty::RawPtr(element, mutability) = self.body.local_decls[input].ty.kind() else {
            return None;
        };
        if *mutability != Mutability::Not || *element != self.tcx.types.u8 {
            return None;
        }
        Some((input, position))
    }

    fn has_slice_bounds_check(&self, input: Local, position: Local, tag_block: BasicBlock) -> bool {
        self.body.basic_blocks.iter_enumerated().any(|(bb, data)| {
            let TerminatorKind::Assert {
                msg: AssertKind::BoundsCheck { index, .. },
                target,
                ..
            } = &data.terminator().kind
            else {
                return false;
            };
            let index_matches = self.operand_local(index).is_some_and(|value| {
                self.canonical(value) == self.canonical(position)
            });
            let input_is_slice = matches!(self.body.local_decls[input].ty.kind(), ty::Ref(_, pointee, _) if matches!(pointee.kind(), ty::Slice(element) if *element == self.tcx.types.u8));
            index_matches && input_is_slice && self.dominators.dominates(*target, tag_block) && self.dominators.dominates(bb, tag_block)
        })
    }

    fn table_entry(&self, tag: Local) -> Option<Local> {
        for local in self.definitions.indices() {
            let Some(definition) = self.definitions[local] else { continue };
            let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) = definition.rvalue else {
                continue;
            };
            tracing::info!(?local, ?place, ty = ?place.ty(self.body, self.tcx).ty, "table-entry read candidate");
            if place.ty(self.body, self.tcx).ty != self.tcx.types.u16 {
                continue;
            }
            match place.projection.as_ref() {
                [ProjectionElem::Index(index)] if self.equivalent_through_cast(*index, tag) => {
                    let base_ty = self.body.local_decls[place.local].ty;
                    if matches!(base_ty.kind(), ty::Array(element, length) if *element == self.tcx.types.u16 && length.try_to_target_usize(self.tcx) == Some(256)) {
                        return Some(local);
                    }
                }
                [ProjectionElem::Deref] => {
                    let Some((table, index)) = self.pointer_offset(place.local) else { continue };
                    let ty::RawPtr(element, mutability) = self.body.local_decls[table].ty.kind() else {
                        continue;
                    };
                    if *mutability == Mutability::Not
                        && *element == self.tcx.types.u16
                        && self.equivalent_through_cast(index, tag)
                    {
                        return Some(local);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn loaded_trailer(&self, input: Local, position: Local) -> Option<Local> {
        for loaded in self.definitions.indices() {
            let Some(definition) = self.definitions[loaded] else { continue };
            let Rvalue::Cast(CastKind::Transmute, raw, ty) = definition.rvalue else { continue };
            if *ty != self.tcx.types.u32 {
                continue;
            }
            let Some(raw_local) = self.operand_local(raw) else { continue };
            let Some(raw_definition) = self.definitions[raw_local] else { continue };
            let Rvalue::Use(Operand::Copy(raw_place) | Operand::Move(raw_place), _) = raw_definition.rvalue else {
                continue;
            };
            let [ProjectionElem::Deref] = raw_place.projection.as_ref() else { continue };
            let byte_pointer = self.peel_copy_cast(raw_place.local);
            let Some((base, trailer_position)) = self.pointer_offset(byte_pointer) else {
                continue;
            };
            let position_matches = self.add_operands(trailer_position).is_some_and(|(left, right)| {
                (self.operand_local(left).is_some_and(|value| self.equivalent_through_cast(value, position)) && self.integer_constant(right) == Some(1))
                    || (self.operand_local(right).is_some_and(|value| self.equivalent_through_cast(value, position)) && self.integer_constant(left) == Some(1))
            });
            if !position_matches {
                continue;
            }
            let base = self.peel_copy_cast(base);
            let base_definition = self.definitions[base];
            let base_matches = self.canonical(base) == self.canonical(input)
                || base_definition.is_some_and(|definition| match definition.rvalue {
                    Rvalue::RawPtr(RawPtrKind::Const, place) => {
                        self.canonical(self.peel_copy_cast(place.local)) == self.canonical(input)
                    }
                    _ => false,
                });
            if base_matches {
                return Some(loaded);
            }
        }
        None
    }

    fn mask_chain(&self, tag_type: Local, loaded: Local) -> bool {
        let Some(multiplied) = self.definitions.indices().find(|&local| {
            let Some((left, right)) = self.binary_operands(local, BinOp::Mul) else {
                return false;
            };
            (self.operand_local(left).is_some_and(|value| self.same_value(value, tag_type))
                && self.integer_constant(right) == Some(8))
                || (self.operand_local(right).is_some_and(|value| self.same_value(value, tag_type))
                    && self.integer_constant(left) == Some(8))
        }) else {
            return false;
        };
        let shifted = self.definitions.indices().any(|local| {
            let Some((left, right)) = self.binary_operands(local, BinOp::Shl) else {
                return false;
            };
            self.integer_constant(left) == Some(1)
                && self.operand_local(right).is_some_and(|value| self.same_value(value, multiplied))
        });
        let loaded_masked = self.definitions.indices().any(|local| {
            let Some((left, right)) = self.binary_operands(local, BinOp::BitAnd) else {
                return false;
            };
            self.operand_local(left).is_some_and(|value| self.same_value(value, loaded))
                || self.operand_local(right).is_some_and(|value| self.same_value(value, loaded))
        });
        shifted && loaded_masked
    }

    fn candidate_loops(&self) -> Vec<(BasicBlock, BasicBlock)> {
        let mut latches: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        for (latch, data) in traversal::reachable(self.body) {
            for successor in data.terminator().successors() {
                if self.dominators.dominates(successor, latch) {
                    latches.entry(successor).or_default().push(latch);
                }
            }
        }
        let mut result = Vec::new();
        for header in self.body.basic_blocks.indices() {
            let Some(latches) = latches.get(&header) else { continue };
            if let [latch] = latches.as_slice() {
                result.push((header, *latch));
            }
        }
        result
    }

    fn prove(&self) -> Vec<MirLoopPreloadProof> {
        for local in self.definitions.indices() {
            if let Some(definition) = self.definitions[local] {
                tracing::info!(
                    ?local,
                    ?definition.location,
                    rvalue = ?definition.rvalue,
                    "MIR loop-preload definition"
                );
            }
        }
        let loops = self.candidate_loops();
        let mut proofs = Vec::new();
        tracing::info!(?loops, "loop preload natural-loop candidates");
        for (header, latch) in loops {
            for tag in self.definitions.indices() {
                let Some(definition) = self.definitions[tag] else { continue };
                let Some((input, position, is_slice)) = self
                    .slice_tag(tag)
                    .map(|(input, position)| (input, position, true))
                    .or_else(|| self.raw_tag(tag).map(|(input, position)| (input, position, false)))
                else {
                    continue;
                };
                if !self.dominators.dominates(header, definition.location.block)
                    || !self.dominators.dominates(definition.location.block, latch)
                {
                    continue;
                }
                if is_slice
                    && !self.has_slice_bounds_check(input, position, definition.location.block)
                {
                    continue;
                }
                let Some(tag_type) = self.find_tag_type(tag) else {
                    tracing::info!(?tag, "reject: no tag type");
                    continue;
                };
                let Some(entry) = self.table_entry(tag) else {
                    tracing::info!(?tag, "reject: no table entry");
                    continue;
                };
                let Some(loaded) = self.loaded_trailer(input, position) else {
                    tracing::info!(?tag, "reject: no trailer");
                    continue;
                };
                let Some((position_from_update, next_position)) = self.find_position_update(tag_type)
                else {
                    tracing::info!(?tag, ?tag_type, "reject: no position update");
                    continue;
                };
                if !self.same_value(position_from_update, position) {
                    tracing::info!(?tag, ?position, ?position_from_update, "reject: update uses different position");
                    continue;
                }
                if !self.mask_chain(tag_type, loaded) {
                    tracing::info!(?tag, ?tag_type, ?loaded, "reject: no mask chain");
                    continue;
                }
                proofs.push(MirLoopPreloadProof {
                    input,
                    position,
                    tag,
                    tag_type,
                    entry,
                    loaded,
                    next_position,
                    header,
                    latch,
                });
            }
        }
        proofs
    }
}

impl<'tcx> crate::MirPass<'tcx> for LoopPreloadMarker {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() >= 4
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if body.loop_preload_candidate.is_some() || tcx.sess.target.endian != Endian::Little {
            return;
        }
        let proofs = Analyzer::new(tcx, body).prove();
        if let [proof] = proofs.as_slice() {
            tracing::debug!(?proof, "proved MIR loop preload candidate");
            body.loop_preload_candidate = Some(LoopPreloadCandidate::SnappyCopy12Slice);
        }
    }

    fn is_required(&self) -> bool {
        false
    }
}
