//! Term enumeration for automated search.
//!
//! This module provides tools for systematically generating all
//! possible Boolean terms up to a specified depth, useful for
//! exhaustive search, counterexample finding, and automated theorem
//! discovery.
//!
//! # Warning
//!
//! The number of terms grows **exponentially** with depth. Even
//! with modest parameters (e.g., 3 variables at depth 3), millions
//! of terms can be generated. Always use a depth limit or other
//! plan to prevent memory exhaustion.
