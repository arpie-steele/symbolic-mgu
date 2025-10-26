//! Types of error handling.

/// The basic type of the error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MguErrorType {
    /// Metavariable could not be created.
    UnknownMetavariable,

    /// Type mismatch
    TypeMismatch,

    /// Slots mismatch.
    SlotsMismatch,

    /// Type mismatch
    TypeUnassignable,

    /// Indexed item could not be found.
    IndexOutOfRange,

    /// Indexed item could not be found.
    ChildIndexOutOfRange,

    /// Value out of range for conversion to named type.
    SignedValueOutOfRange,

    /// Value out of range for conversion to named type.
    UnsignedValueOutOfRange,

    /// Value out of range for conversion to named type.
    UnsignedValueUnsupported,

    /// Pair Validation Error.
    PairValidationFailure,

    /// Unification failure with descriptive message.
    UnificationFailure,

    /// Distinctness constraint violation.
    DistinctnessViolation,

    /// Substitution contains cycles (variable maps to term containing
    /// itself).
    SubstitutionCycle,

    /// Clique validation error: elements must be in strictly
    /// ascending order.
    CliqueOrderingError,

    /// Clique validation error: must have at least two elements.
    CliqueMinimumSizeError,

    /// Decomposition validation error: contains invalid clique.
    DecompositionValidationError,

    /// Memory allocation error.
    AllocationError,

    /// Numeric conversion error.
    NumericConversionError,

    /// Color parsing error.
    ColorParseError,

    /// Catch-all for bare errors created incorrectly.
    UnknownErrorType,

    /// Catch-all for messages created incorrectly.
    UnknownErrorTypeMessage,

    /// Catch-all error (deprecated - use specific error types instead).
    UnknownError,
}
