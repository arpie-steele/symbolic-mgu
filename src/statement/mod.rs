//! Define the Statement type and operations.
//!
//! This module provides the core [`Statement`] type for representing axioms,
//! inference rules, and theorems, along with operations for proof construction.
//!
//! # Organization
//!
//! - [`base`]: Core Statement struct and accessors
//! - [`substitution`]: Substitution operations with distinctness validation
//! - [`operations`]: Proof construction operations (apply, contract, relabel)
//! - [`compact_proof`]: Compact proof parsing
//! - [`inclusion`]: Statement inclusion and α-equivalence checking
//!
//! # Distinctness Constraints
//!
//! Each [`Statement`] carries a [`DistinctnessGraph`] that records which metavariables
//! must remain "distinct"—they cannot be substituted with terms sharing common
//! metavariables. This prevents invalid substitutions that would conflate logically
//! separate entities.
//!
//! ## How Distinctness Propagates
//!
//! When operations are performed on statements:
//!
//! 1. **Substitution** ([`Statement::substitute`]): For each distinctness constraint
//!    `(x, y)`, validates that the substituted terms don't share metavariables, then
//!    propagates constraints to all metavariable pairs across the two substituted terms.
//!
//! 2. **CONTRACT**: Applies the unifying substitution; distinctness graph transforms
//!    accordingly.
//!
//! 3. **APPLY / `APPLY_MULTIPLE`**: Merges distinctness graphs from all participating
//!    statements (union of edges), after applying the unifying substitution.
//!
//! 4. **RELABEL**: Renames variables in the distinctness graph to match the relabeling.
//!
//! 5. **CONVERT**: Maps distinctness constraints through the variable mapping to the
//!    target type system.
//!
//! ## Validation
//!
//! Distinctness violations are detected during substitution: if terms substituted for
//! two "distinct" variables share any metavariable, an [`MguError::DistinctnessViolation`]
//! is returned.
//!
//! For background on distinctness in formal systems, see the Metamath book or the
//! [`crate::metamath`] module's handling of `$d` statements.
//!
//! [`DistinctnessGraph`]: crate::DistinctnessGraph
//! [`MguError::DistinctnessViolation`]: crate::MguError::DistinctnessViolation

// Sub-modules
mod base;
pub mod compact_proof;
pub mod inclusion;
mod operations;
mod substitution;

// Re-export Statement type
pub use base::Statement;
