use crate::circuits::cell::*;
use crate::circuits::etable::allocator::*;
use crate::circuits::etable::stack_lookup_context::StackReadLookup;
use crate::circuits::etable::ConstraintBuilder;
use crate::circuits::etable::EventTableCommonConfig;
use crate::circuits::etable::EventTableOpcodeConfig;
use crate::circuits::etable::EventTableOpcodeConfigBuilder;
use crate::circuits::utils::bn_to_field;
use crate::circuits::utils::step_status::StepStatus;
use crate::circuits::utils::table_entry::EventTableEntryWithMemoryInfo;
use crate::circuits::utils::Context;
use crate::constant;
use crate::constant_from;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::VirtualCells;
use num_bigint::BigUint;
use specs::etable::EventTableEntry;
use specs::itable::OpcodeClass;
use specs::itable::OPCODE_CLASS_SHIFT;
use specs::mtable::LocationType;
use specs::mtable::VarType;
use specs::step::StepInfo;

pub struct SelectConfig<F: FieldExt> {
    cond_inv: AllocatedUnlimitedCell<F>,

    val1: AllocatedU64Cell<F>,
    res: AllocatedU64Cell<F>,

    cond_lookup: StackReadLookup<F>,
    val2_lookup: StackReadLookup<F>,
    memory_table_lookup_stack_read_val1: AllocatedMemoryTableLookupReadCell<F>,
    memory_table_lookup_stack_write: AllocatedMemoryTableLookupWriteCell<F>,
}

pub struct SelectConfigBuilder {}

impl<F: FieldExt> EventTableOpcodeConfigBuilder<F> for SelectConfigBuilder {
    fn configure(
        common_config: &EventTableCommonConfig<F>,
        allocator: &mut EventTableCellAllocator<F>,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Box<dyn EventTableOpcodeConfig<F>> {
        let mut stack_lookup_context = common_config.stack_lookup_context.clone();

        let cond_lookup = stack_lookup_context.pop(constraint_builder).unwrap();
        let val2_lookup = stack_lookup_context.pop(constraint_builder).unwrap();

        let cond_inv = allocator.alloc_unlimited_cell();

        let val1 = allocator.alloc_u64_cell();
        let res = allocator.alloc_u64_cell();
        let is_i32 = val2_lookup.is_i32;

        constraint_builder.push(
            "select: cond is zero",
            Box::new(move |meta| {
                vec![
                    (constant_from!(1)
                        - cond_lookup.value.u64_cell.expr(meta) * cond_inv.expr(meta))
                        * (res.u64_cell.expr(meta) - val2_lookup.value.u64_cell.expr(meta)),
                ]
            }),
        );

        constraint_builder.push(
            "select: cond is not zero",
            Box::new(move |meta| {
                vec![
                    cond_lookup.value.u64_cell.expr(meta)
                        * (res.u64_cell.expr(meta) - val1.u64_cell.expr(meta)),
                ]
            }),
        );

        let eid = common_config.eid_cell;
        let sp = common_config.sp_cell;

        let memory_table_lookup_stack_read_val1 = allocator.alloc_memory_table_lookup_read_cell(
            "op_select stack read",
            constraint_builder,
            eid,
            move |____| constant_from!(LocationType::Stack as u64),
            move |meta| sp.expr(meta) + constant_from!(3),
            move |meta| is_i32.expr(meta),
            move |meta| val1.u64_cell.expr(meta),
            move |____| constant_from!(1),
        );

        let memory_table_lookup_stack_write = allocator.alloc_memory_table_lookup_write_cell(
            "op_select stack write",
            constraint_builder,
            eid,
            move |____| constant_from!(LocationType::Stack as u64),
            move |meta| sp.expr(meta) + constant_from!(3),
            move |meta| is_i32.expr(meta),
            move |meta| res.u64_cell.expr(meta),
            move |____| constant_from!(1),
        );

        Box::new(SelectConfig {
            cond_inv,
            val1,
            res,
            cond_lookup,
            val2_lookup,
            memory_table_lookup_stack_read_val1,
            memory_table_lookup_stack_write,
        })
    }
}

impl<F: FieldExt> EventTableOpcodeConfig<F> for SelectConfig<F> {
    fn opcode(&self, _: &mut VirtualCells<'_, F>) -> Expression<F> {
        constant!(bn_to_field(
            &(BigUint::from(OpcodeClass::Select as u64) << OPCODE_CLASS_SHIFT)
        ))
    }

    fn assign(
        &self,
        ctx: &mut Context<'_, F>,
        step: &StepStatus,
        entry: &EventTableEntryWithMemoryInfo,
    ) -> Result<(), Error> {
        match &entry.eentry.step_info {
            StepInfo::Select {
                val1,
                val2,
                cond,
                result,
                vtype,
            } => {
                self.val1.assign(ctx, *val1)?;
                self.cond_inv
                    .assign(ctx, F::from(*cond).invert().unwrap_or(F::zero()))?;
                self.res.assign(ctx, *result)?;

                self.cond_lookup.assign(
                    ctx,
                    entry.memory_rw_entires[0].start_eid,
                    step.current.eid,
                    entry.memory_rw_entires[0].end_eid,
                    step.current.sp + 1,
                    true,
                    *cond,
                )?;

                self.val2_lookup.assign(
                    ctx,
                    entry.memory_rw_entires[1].start_eid,
                    step.current.eid,
                    entry.memory_rw_entires[1].end_eid,
                    step.current.sp + 2,
                    *vtype == VarType::I32,
                    *val2,
                )?;

                self.memory_table_lookup_stack_read_val1.assign(
                    ctx,
                    entry.memory_rw_entires[2].start_eid,
                    step.current.eid,
                    entry.memory_rw_entires[2].end_eid,
                    step.current.sp + 3,
                    LocationType::Stack,
                    *vtype == VarType::I32,
                    *val1,
                )?;

                self.memory_table_lookup_stack_write.assign(
                    ctx,
                    step.current.eid,
                    entry.memory_rw_entires[3].end_eid,
                    step.current.sp + 3,
                    LocationType::Stack,
                    *vtype == VarType::I32,
                    *result,
                )?;

                Ok(())
            }

            _ => unreachable!(),
        }
    }

    fn sp_diff(&self, _meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(constant_from!(2))
    }

    fn mops(&self, _meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(constant_from!(1))
    }

    fn memory_writing_ops(&self, _: &EventTableEntry) -> u32 {
        1
    }
}
