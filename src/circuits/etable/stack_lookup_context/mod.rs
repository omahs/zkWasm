use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Expression;
use halo2_proofs::plonk::VirtualCells;
use specs::encode::memory_table::encode_memory_table_entry;
use specs::mtable::LocationType;

use crate::circuits::cell::AllocatedBitCell;
use crate::circuits::cell::AllocatedCommonRangeCell;
use crate::circuits::cell::AllocatedU64Cell;
use crate::circuits::cell::AllocatedUnlimitedCell;
use crate::circuits::cell::CellExpression;
use crate::circuits::utils::Context;
use crate::constant_from;

use super::allocator::AllocatedMemoryTableLookupReadCell;
use super::allocator::EventTableCellAllocator;
use super::allocator::EventTableCellType;
use super::constraint_builder::ConstraintBuilder;

const POP_NUM: usize = 2;

#[derive(Clone)]
pub(in crate::circuits::etable) struct StackReadLookup<F: FieldExt> {
    pub(in crate::circuits::etable) value: AllocatedU64Cell<F>,
    pub(in crate::circuits::etable) is_i32: AllocatedBitCell<F>,
    pub(in crate::circuits::etable) lookup_cell: AllocatedMemoryTableLookupReadCell<F>,
    pub(in crate::circuits::etable) enable: AllocatedBitCell<F>,
}

impl<F: FieldExt> StackReadLookup<F> {
    pub(in crate::circuits::etable) fn assign(
        &self,
        ctx: &mut Context<'_, F>,
        start_eid: u32,
        eid: u32,
        end_eid: u32,
        offset: u32,
        is_i32: bool,
        value: u64,
    ) -> Result<(), Error> {
        self.enable.assign_bool(ctx, true)?;
        self.value.assign(ctx, value)?;
        self.is_i32.assign_bool(ctx, is_i32)?;

        self.lookup_cell.assign(
            ctx,
            start_eid,
            eid,
            end_eid,
            offset,
            LocationType::Stack,
            is_i32,
            value,
        )?;

        Ok(())
    }

    pub(in crate::circuits::etable) fn equal_vartype(
        &self,
        constraint_builder: &mut ConstraintBuilder<F>,
        other: &StackReadLookup<F>,
    ) {
        let source_is_32 = self.is_i32.clone();
        let target_is_i32 = other.is_i32.clone();

        constraint_builder.push(
            "stack_read_lookup: equal vartype",
            Box::new(move |meta| vec![source_is_32.expr(meta) - target_is_i32.expr(meta)]),
        )
    }
}

#[derive(Clone)]
pub(in crate::circuits::etable) struct StackLookupContext<F: FieldExt> {
    stack_read_lookups: Vec<StackReadLookup<F>>,
}

impl<F: FieldExt> StackLookupContext<F> {
    pub(in crate::circuits::etable) fn new(allocator: &mut EventTableCellAllocator<F>) -> Self {
        let stack_read_lookups = [(); POP_NUM]
            .into_iter()
            .map(|_| StackReadLookup {
                value: allocator.alloc_u64_cell(),
                is_i32: allocator.alloc_bit_cell(),
                lookup_cell: AllocatedMemoryTableLookupReadCell {
                    encode_cell: AllocatedUnlimitedCell(
                        allocator.alloc(&EventTableCellType::MTableLookup),
                    ),
                    start_eid_cell: allocator.alloc_common_range_cell(),
                    end_eid_cell: allocator.alloc_common_range_cell(),
                    start_eid_diff_cell: allocator.alloc_common_range_cell(),
                    end_eid_diff_cell: allocator.alloc_common_range_cell(),
                },
                enable: allocator.alloc_bit_cell(),
            })
            .collect::<Vec<_>>();

        Self { stack_read_lookups }
    }

    pub(in crate::circuits::etable) fn configure(
        &self,
        meta: &mut ConstraintSystem<F>,
        eid: &AllocatedCommonRangeCell<F>,
        sp_cell: &AllocatedCommonRangeCell<F>,
        selector: impl Fn(&mut VirtualCells<F>) -> Expression<F>,
    ) {
        for (depth, stack) in self.stack_read_lookups.iter().rev().enumerate() {
            meta.create_gate("stack_lookup_context: pop", |meta| {
                vec![
                    (eid.expr(meta)
                        - stack.lookup_cell.start_eid_cell.expr(meta)
                        - stack.lookup_cell.start_eid_diff_cell.expr(meta)
                        - constant_from!(1))
                        * stack.enable.expr(meta)
                        * selector(meta),
                    (eid.expr(meta) + stack.lookup_cell.end_eid_diff_cell.expr(meta)
                        - stack.lookup_cell.end_eid_cell.expr(meta))
                        * stack.enable.expr(meta)
                        * selector(meta),
                    (encode_memory_table_entry(
                        stack.lookup_cell.start_eid_cell.expr(meta),
                        stack.lookup_cell.end_eid_cell.expr(meta),
                        sp_cell.expr(meta) + constant_from!(1 + depth),
                        constant_from!(LocationType::Stack as u64),
                        stack.is_i32.expr(meta),
                        stack.value.expr(meta),
                    ) - stack.lookup_cell.encode_cell.expr(meta))
                        * stack.enable.expr(meta)
                        * selector(meta),
                ]
            })
        }
    }

    pub(in crate::circuits::etable) fn pop(
        &mut self,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Option<StackReadLookup<F>> {
        let stack_read_lookup: Option<StackReadLookup<F>> = self.stack_read_lookups.pop();

        if let Some(cell) = stack_read_lookup.clone() {
            constraint_builder.push(
                "active stack read lookup",
                Box::new(move |meta| vec![cell.enable.expr(meta) - constant_from!(1)]),
            )
        };

        stack_read_lookup
    }

    pub(in crate::circuits::etable) fn pop2(
        &mut self,
        constraint_builder: &mut ConstraintBuilder<F>,
        enable: impl FnOnce(&mut VirtualCells<F>) -> Expression<F> + 'static,
    ) -> Option<StackReadLookup<F>> {
        let stack_read_lookup: Option<StackReadLookup<F>> = self.stack_read_lookups.pop();

        if let Some(cell) = stack_read_lookup.clone() {
            constraint_builder.push(
                "active stack read lookup",
                Box::new(move |meta| vec![cell.enable.expr(meta) - enable(meta)]),
            )
        };

        stack_read_lookup
    }
}
