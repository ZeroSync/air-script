use parser::ast::{BoundaryStmt, TransitionStmt};
pub use parser::ast::{
    self, boundary_constraints::BoundaryExpr, constants::Constant, Identifier, PublicInput,
};
use std::collections::BTreeMap;

mod symbol_table;
use symbol_table::{IdentifierType, SymbolTable};

pub mod boundary_stmts;
use boundary_stmts::BoundaryStmts;

pub mod transition_stmts;
use transition_stmts::{AlgebraicGraph, TransitionStmts, MIN_CYCLE_LENGTH};
pub use transition_stmts::{NodeIndex, TransitionConstraintDegree};

mod error;
use error::SemanticError;

mod helpers;
use helpers::SourceValidator;

#[cfg(test)]
mod tests;

pub type TraceSegment = u8;
pub type Constants = Vec<Constant>;
pub type PublicInputs = Vec<(String, usize)>;
pub type PeriodicColumns = Vec<Vec<u64>>;

/// Internal representation of an AIR.
///
/// TODO: docs
#[derive(Default, Debug)]
pub struct AirIR {
    air_name: String,
    //TODO: remove dead code attribute
    #[allow(dead_code)]
    constants: Constants,
    public_inputs: PublicInputs,
    periodic_columns: PeriodicColumns,
    boundary_stmts: BoundaryStmts,
    transition_stmts: TransitionStmts,
}

impl AirIR {
    // --- CONSTRUCTOR ----------------------------------------------------------------------------

    /// Consumes the provided source and generates a matching AirIR.
    pub fn from_source(source: &ast::Source) -> Result<Self, SemanticError> {
        let ast::Source(source) = source;

        // set a default name.
        let mut air_name = "CustomAir";

        let mut validator = SourceValidator::new();

        // process the declarations of identifiers first, using a single symbol table to enforce
        // uniqueness.
        let mut symbol_table = SymbolTable::default();

        for section in source {
            match section {
                ast::SourceSection::AirDef(Identifier(air_def)) => {
                    // update the name of the air.
                    air_name = air_def;
                }
                ast::SourceSection::Constants(constants) => {
                    symbol_table.insert_constants(constants)?;
                }
                ast::SourceSection::TraceCols(columns) => {
                    // process & validate the main trace columns
                    symbol_table.insert_trace_columns(0, &columns.main_cols)?;
                    // process & validate the auxiliary trace columns
                    symbol_table.insert_trace_columns(1, &columns.aux_cols)?;
                    validator.exists("trace_columns");
                }
                ast::SourceSection::PublicInputs(inputs) => {
                    // process & validate the public inputs
                    symbol_table.insert_public_inputs(inputs)?;
                    validator.exists("public_inputs");
                }
                ast::SourceSection::PeriodicColumns(columns) => {
                    // process & validate the periodic columns
                    symbol_table.insert_periodic_columns(columns)?;
                }
                _ => {}
            }
        }

        // then process the constraints & validate them against the symbol table.
        let mut boundary_stmts = BoundaryStmts::default();
        let mut transition_stmts = TransitionStmts::default();
        for section in source {
            match section {
                ast::SourceSection::BoundaryConstraints(stmts) => {
                    for stmt in stmts {
                        boundary_stmts.insert(&symbol_table, stmt)?
                    }
                    validator.exists("boundary_constraints");
                }
                ast::SourceSection::TransitionConstraints(stmts) => {
                    for stmt in stmts {
                        transition_stmts.insert(&symbol_table, stmt)?
                    }
                    validator.exists("transition_constraints");
                }
                _ => {}
            }
        }

        let (constants, public_inputs, periodic_columns) = symbol_table.into_declarations();

        // validate sections
        validator.check()?;

        Ok(Self {
            air_name: air_name.to_string(),
            constants,
            public_inputs,
            periodic_columns,
            boundary_stmts,
            transition_stmts,
        })
    }

    // --- PUBLIC ACCESSORS -----------------------------------------------------------------------

    pub fn air_name(&self) -> &str {
        &self.air_name
    }

    pub fn constants(&self) -> &Constants {
        &self.constants
    }

    pub fn public_inputs(&self) -> &PublicInputs {
        &self.public_inputs
    }

    pub fn periodic_columns(&self) -> &PeriodicColumns {
        &self.periodic_columns
    }

    // --- PUBLIC ACCESSORS FOR BOUNDARY CONSTRAINTS ----------------------------------------------

    pub fn num_main_assertions(&self) -> usize {
        self.boundary_stmts.num_constraints_first(0) + self.boundary_stmts.num_constraints_last(0)
    }

    pub fn num_aux_assertions(&self) -> usize {
        self.boundary_stmts.num_constraints_first(1) + self.boundary_stmts.num_constraints_last(1)
    }

    // --- PUBLIC ACCESSORS FOR TRANSITION CONSTRAINTS --------------------------------------------

    pub fn constraint_degrees(
        &self,
        trace_segment: TraceSegment,
    ) -> Vec<TransitionConstraintDegree> {
        self.transition_stmts
            .constraint_degrees(trace_segment)
    }

    pub fn transition_constraints(&self, trace_segment: TraceSegment) -> &[NodeIndex] {
        self.transition_stmts.transition_constraints(trace_segment)
    }

    pub fn transition_graph(&self) -> &AlgebraicGraph {
        self.transition_stmts.graph()
    }
}
