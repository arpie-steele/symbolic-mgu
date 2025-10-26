//! Boolean evaluation of terms.
//!
//! This module provides functionality for evaluating terms where
//! all metavariables and nodes are boolean-valued. It supports
//! tautology testing and truth table evaluation using bit-wise
//! operations on primitive unsigned integers and `BigUint`.
//!
//! # Future Enhancements
//!
//! The evaluator could be enhanced with structural short-circuit
//! evaluation for tautological patterns:
//!
//! - **`φ → φ`**: Always true (any term implies itself)
//! - **`φ ↔ φ`**: Always true (any term is equivalent to itself)
//!
//! This would enable verification of definitions involving these
//! patterns without requiring full evaluation of the sub-terms.
//! For example, the True definition `⊤ ↔ (∀x x = x → ∀x x = x)`
//! contains the pattern `ψ → ψ` where `ψ = ∀x x = x`, which could
//! be recognized as tautological regardless of whether `ψ` contains
//! quantifiers or other non-propositional constructs.
//!
//! Implementation approach:
//! 1. Before evaluating `Implies(a, b)` or `Biimp(a, b)`, check
//!    if `a` and `b` are structurally identical Boolean-valued
//!    terms
//! 2. If identical, return `true_value(num_bits)` immediately
//!    without recursion
//! 3. Otherwise, proceed with normal evaluation
//!
//! This would require adding an equality check (e.g., `a == b`
//! where `a` and `b` are `EnumTerm` references) before the evaluation
//! logic in `eval_implies` and `eval_biimp` within the `eval_map`
//! function.
