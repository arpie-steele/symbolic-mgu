//! Common error handling.

use crate::Type;
use thiserror::Error;

/// The common error type of the entire crate.
///
/// # Questions and Answers
///
/// > If a unification fails in CONTRACT or APPLY, the caller handles the error.
/// > Do you define failure types (e.g. “distinctness conflict”, “type mismatch”,
/// > “no MGU”) separately, or just use a binary success/failure signal?
/// > Could fine-grained error types improve diagnostics or debugging?
///
/// If we write this in Rust, we will definitely want fine-grained error types
/// for debugging, as we are completely dependent on user choice of which STATEMENTS
/// to supply as axioms to determine the legality of CONTRACT and APPLY.
#[derive(Error, Clone, Debug, PartialEq)]
pub enum MguError {
    /// Metavariable could not be created.
    #[error("Unknown Metavariable of type {0}: {1}.")]
    UnknownMetavariable(&'static str, String), // type_name, var_info

    /// Type mismatch
    #[error("Type mismatch. {0} was not the expected {1}.")]
    TypeMismatch(Type, Type), // found_type, expected_type

    /// Slots mismatch.
    #[error("Slots mismatch. {0} children supplied to a node with {1} slots.")]
    SlotsMismatch(usize, usize), // n_children, n_slots

    /// Type mismatch
    #[error("Type mismatch. A tree of type {0} cannot be assigned to a slot of type {1}.")]
    TypeUnassignable(Type, Type), // tree_type, slot_or_var_type

    /// Indexed item could not be found.
    #[error("For type {0:?}, index {1} >= available options {2}.")]
    IndexOutOfRange(Type, usize, usize), // the_type, index, n_options

    /// Indexed item could not be found.
    #[error("Index {0} >= available options {1}.")]
    ChildIndexOutOfRange(usize, usize), // index, n_options

    /// Value out of range for conversion to named type.
    #[error("The value {0} is out-of-range for conversion to {1} (wanted {2}..={3}).")]
    SignedValueOutOfRange(i128, &'static str, u32, u32), // value, dest_type, min, max

    /// Value out of range for conversion to named type.
    #[error("The value {0} is out-of-range for conversion to {1} (wanted {2}..={3}).")]
    UnsignedValueOutOfRange(u128, &'static str, u32, u32), // value, dest_type, min, max

    /// Value out of range for conversion to named type.
    #[error("The value {0} is not supported for conversion to {1}.")]
    UnsignedValueUnsupported(u128, &'static str), // value, dest_type

    /// Pair Validation Error.
    #[error("Elements {0} and {1} are equal or cannot be ordered.")]
    PairValidationFailure(String, String), // element0, element1

    /// Unification failure with descriptive message.
    #[error("Unification failed: {0}")]
    UnificationFailure(String), // msg

    /// Distinctness constraint violation.
    #[error("Distinctness violation: {0}")]
    DistinctnessViolation(String), // msg

    /// Substitution contains cycles (variable maps to term containing itself).
    #[error("Substitution cycle detected: {0}")]
    SubstitutionCycle(String), // msg

    /// Clique validation error: elements must be in strictly ascending order.
    #[error("Clique elements must be in strictly ascending order")]
    CliqueOrderingError,

    /// Clique validation error: must have at least two elements.
    #[error("Clique must contain at least two elements")]
    CliqueMinimumSizeError,

    /// Decomposition validation error: contains invalid clique.
    #[error("Decomposition contains an invalid clique")]
    DecompositionValidationError,

    /// Memory allocation error.
    #[error("Memory allocation failed: {0}")]
    AllocationError(String), // msg

    /// Numeric conversion error.
    #[error("Numeric conversion failed: {0}")]
    NumericConversionError(String), // msg

    /// Color parsing error.
    #[error("Color parsing error: {0}")]
    ColorParseError(String), // msg

    /// Catch-all error (deprecated - use specific error types instead).
    #[error("Unknown Error with code = {0}.")]
    UnknownError(usize), // code
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn unknown_error() {
        let x = MguError::UnknownError(1859usize);
        let s = format!("{x}");
        assert_eq!(s, "Unknown Error with code = 1859.".to_owned());
        let s = format!("{x:?}");
        assert_eq!(s, "UnknownError(1859)".to_owned());
    }
}
