use crate::circuits::cell::*;
use crate::circuits::etable::allocator::*;
use crate::circuits::etable::stack_lookup_context::StackReadLookup;
use crate::circuits::etable::ConstraintBuilder;
use crate::circuits::etable::EventTableCommonConfig;
use crate::circuits::etable::EventTableOpcodeConfig;
use crate::circuits::etable::EventTableOpcodeConfigBuilder;
use crate::circuits::utils::step_status::StepStatus;
use crate::circuits::utils::table_entry::EventTableEntryWithMemoryInfo;
use crate::circuits::utils::Context;
use crate::constant_from;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::VirtualCells;
use specs::encode::opcode::encode_br;
use specs::etable::EventTableEntry;
use specs::mtable::LocationType;
use specs::mtable::VarType;
use specs::step::StepInfo;

pub struct BrConfig<F: FieldExt> {
    keep_cell: AllocatedBitCell<F>,
    drop_cell: AllocatedCommonRangeCell<F>,
    dst_pc_cell: AllocatedCommonRangeCell<F>,
    keep_value_lookup: StackReadLookup<F>,
    memory_table_lookup_stack_write: AllocatedMemoryTableLookupWriteCell<F>,
}

pub struct BrConfigBuilder;

impl<F: FieldExt> EventTableOpcodeConfigBuilder<F> for BrConfigBuilder {
    fn configure(
        common_config: &EventTableCommonConfig<F>,
        allocator: &mut EventTableCellAllocator<F>,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Box<dyn EventTableOpcodeConfig<F>> {
        let mut stack_lookup_context = common_config.stack_lookup_context.clone();

        let keep_cell = allocator.alloc_bit_cell();
        let drop_cell = allocator.alloc_common_range_cell();
        let dst_pc_cell = allocator.alloc_common_range_cell();

        let eid = common_config.eid_cell;
        let sp = common_config.sp_cell;

        let keep_value_lookup = stack_lookup_context
            .pop2(constraint_builder, move |meta| keep_cell.expr(meta))
            .unwrap();

        let memory_table_lookup_stack_write = allocator.alloc_memory_table_lookup_write_cell(
            "op_br stack write",
            constraint_builder,
            eid,
            move |____| constant_from!(LocationType::Stack as u64),
            move |meta| sp.expr(meta) + drop_cell.expr(meta) + constant_from!(1),
            move |meta| keep_value_lookup.is_i32.expr(meta),
            move |meta| keep_value_lookup.value.u64_cell.expr(meta),
            move |meta| keep_cell.expr(meta),
        );

        Box::new(BrConfig {
            keep_cell,
            drop_cell,
            dst_pc_cell,
            keep_value_lookup,
            memory_table_lookup_stack_write,
        })
    }
}

impl<F: FieldExt> EventTableOpcodeConfig<F> for BrConfig<F> {
    fn opcode(&self, meta: &mut VirtualCells<'_, F>) -> Expression<F> {
        encode_br(
            self.drop_cell.expr(meta),
            self.keep_cell.expr(meta),
            self.dst_pc_cell.expr(meta),
        )
    }

    fn assign(
        &self,
        ctx: &mut Context<'_, F>,
        step: &StepStatus,
        entry: &EventTableEntryWithMemoryInfo,
    ) -> Result<(), Error> {
        match &entry.eentry.step_info {
            StepInfo::Br {
                drop,
                keep,
                keep_values,
                dst_pc,
                ..
            } => {
                assert!(keep.len() <= 1);

                self.drop_cell.assign(ctx, F::from(*drop as u64))?;

                if keep.len() > 0 {
                    self.keep_cell.assign(ctx, F::one())?;

                    self.keep_value_lookup.assign(
                        ctx,
                        entry.memory_rw_entires[0].start_eid,
                        step.current.eid,
                        entry.memory_rw_entires[0].end_eid,
                        step.current.sp + 1,
                        VarType::from(keep[0]) == VarType::I32,
                        keep_values[0],
                    )?;

                    self.memory_table_lookup_stack_write.assign(
                        ctx,
                        step.current.eid,
                        entry.memory_rw_entires[1].end_eid,
                        step.current.sp + *drop + 1,
                        LocationType::Stack,
                        VarType::from(keep[0]) == VarType::I32,
                        keep_values[0],
                    )?;
                }

                self.dst_pc_cell.assign(ctx, F::from((*dst_pc) as u64))?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn sp_diff(&self, meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(self.drop_cell.expr(meta))
    }

    fn mops(&self, meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(self.keep_cell.expr(meta))
    }

    fn memory_writing_ops(&self, entry: &EventTableEntry) -> u32 {
        match &entry.step_info {
            StepInfo::Br { keep, .. } => keep.len() as u32,
            _ => unreachable!(),
        }
    }

    fn next_iid(
        &self,
        meta: &mut VirtualCells<'_, F>,
        _: &EventTableCommonConfig<F>,
    ) -> Option<Expression<F>> {
        Some(self.dst_pc_cell.expr(meta))
    }
}
