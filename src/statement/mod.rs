//! Define the Statement type and operations.
//!
//! This module provides the core [`Statement`] type for representing axioms,
//! inference rules, and theorems, along with operations for proof construction.
//!
//! # Organization
//!
//! - [`base`]: Core Statement struct and accessors
//! - [`substitution`]: Substitution operations
//! - [`operations`]: Proof construction operations (apply, contract, relabel)
//! - [`compact_proof`]: Compact proof parsing
//! - [`inclusion`]: Statement inclusion and α-equivalence checking

// Submodules
mod base;
mod substitution;
mod operations;
pub mod compact_proof;
pub mod inclusion;

// Re-export Statement type
pub use base::Statement;
