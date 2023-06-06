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
use crate::constant;
use crate::constant_from;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::VirtualCells;
use specs::encode::opcode::encode_global_set;
use specs::etable::EventTableEntry;
use specs::mtable::LocationType;
use specs::mtable::VarType;
use specs::step::StepInfo;

pub struct GlobalSetConfig<F: FieldExt> {
    idx_cell: AllocatedCommonRangeCell<F>,
    stack_reading_lookup: StackReadLookup<F>,
    memory_table_lookup_global_write: AllocatedMemoryTableLookupWriteCell<F>,
}

pub struct GlobalSetConfigBuilder {}

impl<F: FieldExt> EventTableOpcodeConfigBuilder<F> for GlobalSetConfigBuilder {
    fn configure(
        common_config: &EventTableCommonConfig<F>,
        allocator: &mut EventTableCellAllocator<F>,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Box<dyn EventTableOpcodeConfig<F>> {
        let mut stack_lookup_context = common_config.stack_lookup_context.clone();

        let stack_reading_lookup = stack_lookup_context.pop(constraint_builder).unwrap();
        let is_i32_cell = stack_reading_lookup.is_i32;
        let idx_cell = allocator.alloc_common_range_cell();

        let eid_cell = common_config.eid_cell;

        let memory_table_lookup_global_write = allocator.alloc_memory_table_lookup_write_cell(
            "op_global_set global write",
            constraint_builder,
            eid_cell,
            move |____| constant_from!(LocationType::Global as u64),
            move |meta| idx_cell.expr(meta),
            move |meta| is_i32_cell.expr(meta),
            move |meta| stack_reading_lookup.value.expr(meta),
            move |____| constant_from!(1),
        );

        Box::new(GlobalSetConfig {
            idx_cell,
            stack_reading_lookup,
            memory_table_lookup_global_write,
        })
    }
}

impl<F: FieldExt> EventTableOpcodeConfig<F> for GlobalSetConfig<F> {
    fn opcode(&self, meta: &mut VirtualCells<'_, F>) -> Expression<F> {
        encode_global_set(self.idx_cell.expr(meta))
    }

    fn assign(
        &self,
        ctx: &mut Context<'_, F>,
        step: &StepStatus,
        entry: &EventTableEntryWithMemoryInfo,
    ) -> Result<(), Error> {
        match &entry.eentry.step_info {
            StepInfo::SetGlobal {
                idx, vtype, value, ..
            } => {
                self.idx_cell.assign(ctx, F::from(*idx as u64))?;

                self.stack_reading_lookup.assign(
                    ctx,
                    entry.memory_rw_entires[0].start_eid,
                    step.current.eid,
                    entry.memory_rw_entires[0].end_eid,
                    step.current.sp + 1,
                    *vtype == VarType::I32,
                    *value,
                )?;

                self.memory_table_lookup_global_write.assign(
                    ctx,
                    step.current.eid,
                    entry.memory_rw_entires[1].end_eid,
                    *idx,
                    LocationType::Global,
                    *vtype == VarType::I32,
                    *value,
                )?;

                Ok(())
            }

            _ => unreachable!(),
        }
    }

    fn sp_diff(&self, _meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(constant!(F::one()))
    }

    fn mops(&self, _meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(constant_from!(1))
    }

    fn memory_writing_ops(&self, _: &EventTableEntry) -> u32 {
        1
    }
}
