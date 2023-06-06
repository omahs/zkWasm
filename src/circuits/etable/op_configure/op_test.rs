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
use specs::itable::TestOp;
use specs::itable::OPCODE_ARG0_SHIFT;
use specs::itable::OPCODE_ARG1_SHIFT;
use specs::itable::OPCODE_CLASS_SHIFT;
use specs::mtable::LocationType;
use specs::mtable::VarType;
use specs::step::StepInfo;

pub struct TestConfig<F: FieldExt> {
    is_32_cell: AllocatedBitCell<F>,
    res_cell: AllocatedBitCell<F>,
    value_inv_cell: AllocatedUnlimitedCell<F>,

    memory_table_lookup_stack_read: StackReadLookup<F>,
    memory_table_lookup_stack_write: AllocatedMemoryTableLookupWriteCell<F>,
}

pub struct TestConfigBuilder {}

impl<F: FieldExt> EventTableOpcodeConfigBuilder<F> for TestConfigBuilder {
    fn configure(
        common_config: &EventTableCommonConfig<F>,
        allocator: &mut EventTableCellAllocator<F>,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Box<dyn EventTableOpcodeConfig<F>> {
        let mut stack_lookup_context = common_config.stack_lookup_context.clone();
        let memory_table_lookup_stack_read = stack_lookup_context.pop(constraint_builder).unwrap();

        let is_32_cell = memory_table_lookup_stack_read.is_i32;
        let res_cell = allocator.alloc_bit_cell();
        let value_inv_cell = allocator.alloc_unlimited_cell();

        constraint_builder.constraints.push((
            "op_test res = !value",
            Box::new(move |meta| {
                vec![
                    res_cell.expr(meta) * memory_table_lookup_stack_read.value.u64_cell.expr(meta),
                    memory_table_lookup_stack_read.value.u64_cell.expr(meta)
                        * value_inv_cell.expr(meta)
                        - constant_from!(1)
                        + res_cell.expr(meta),
                ]
            }),
        ));

        let eid = common_config.eid_cell;
        let sp = common_config.sp_cell;

        let memory_table_lookup_stack_write = allocator.alloc_memory_table_lookup_write_cell(
            "op_test stack write",
            constraint_builder,
            eid,
            move |____| constant_from!(LocationType::Stack as u64),
            move |meta| sp.expr(meta) + constant_from!(1),
            move |____| constant_from!(1),
            move |meta| res_cell.expr(meta),
            move |____| constant_from!(1),
        );

        Box::new(TestConfig {
            is_32_cell,
            res_cell,
            value_inv_cell,
            memory_table_lookup_stack_read,
            memory_table_lookup_stack_write,
        })
    }
}

impl<F: FieldExt> EventTableOpcodeConfig<F> for TestConfig<F> {
    fn opcode(&self, meta: &mut VirtualCells<'_, F>) -> Expression<F> {
        constant!(bn_to_field(
            &(BigUint::from(OpcodeClass::Test as u64) << OPCODE_CLASS_SHIFT)
        )) + constant_from!(TestOp::Eqz as u16)
            * constant!(bn_to_field(&(BigUint::from(1u64) << OPCODE_ARG0_SHIFT)))
            + self.memory_table_lookup_stack_read.is_i32.expr(meta)
                * constant!(bn_to_field(&(BigUint::from(1u64) << OPCODE_ARG1_SHIFT)))
    }

    fn assign(
        &self,
        ctx: &mut Context<'_, F>,
        step: &StepStatus,
        entry: &EventTableEntryWithMemoryInfo,
    ) -> Result<(), Error> {
        match &entry.eentry.step_info {
            StepInfo::Test {
                vtype,
                value,
                result,
            } => {
                self.value_inv_cell
                    .assign(ctx, F::from(*value).invert().unwrap_or(F::zero()))?;
                self.res_cell.assign_u32(ctx, *result as u32)?;

                self.memory_table_lookup_stack_read.assign(
                    ctx,
                    entry.memory_rw_entires[0].start_eid,
                    step.current.eid,
                    entry.memory_rw_entires[0].end_eid,
                    step.current.sp + 1,
                    *vtype == VarType::I32,
                    *value,
                )?;

                self.memory_table_lookup_stack_write.assign(
                    ctx,
                    step.current.eid,
                    entry.memory_rw_entires[1].end_eid,
                    step.current.sp + 1,
                    LocationType::Stack,
                    true,
                    *result as u32 as u64,
                )?;

                Ok(())
            }

            _ => unreachable!(),
        }
    }

    fn mops(&self, _meta: &mut VirtualCells<'_, F>) -> Option<Expression<F>> {
        Some(constant_from!(1))
    }

    fn memory_writing_ops(&self, _: &EventTableEntry) -> u32 {
        1
    }
}
