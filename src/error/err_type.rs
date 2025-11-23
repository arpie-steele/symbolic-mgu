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

    /// Argument Error with descriptive message.
    ArgumentError,

    /// Verification failure with descriptive message.
    VerificationFailure,

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

    /// Expected a metavariable but found a node, or vice versa.
    TermKindMismatch,

    /// Node is not a Boolean operation.
    NodeNotBooleanOp,

    /// Invalid Boolean function code for the given arity.
    InvalidBooleanCode,

    /// Boolean operation arity not supported.
    UnsupportedBooleanArity,

    /// Boolean evaluation failed.
    BooleanEvaluationFailed,

    /// Variable not found in the binding list.
    VariableNotBound,

    /// Variable index exceeds the allowed limit.
    VariableIndexOutOfRange,

    /// Unknown node name in factory method.
    UnknownNodeName,

    /// Node type doesn't match expected type.
    NodeTypeMismatch,

    /// Required feature not enabled.
    FeatureRequired,

    /// Type doesn't support the required capability.
    TypeCapabilityUnsupported,

    /// Bit position out of range for truth table.
    BitPositionOutOfRange,

    /// I/O error from file or network operations.
    IoError,

    /// Parse error in database file or data stream.
    ParseError,

    /// Catch-all for bare errors created incorrectly.
    UnknownErrorType,

    /// Catch-all for messages created incorrectly.
    UnknownErrorTypeMessage,

    /// Catch-all error (deprecated - use specific error types instead).
    UnknownError,
}
