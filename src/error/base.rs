//! Common error handling via enum.
//!
//! # Error Construction Best Practices
//!
//! This module provides a comprehensive error type [`MguError`] with multiple variants
//! for different failure modes. To ensure consistency and maintainability, follow these
//! guidelines when creating errors:
//!
//! ## Use Constructors When Available
//!
//! Many error variants have dedicated constructor methods that provide type safety and
//! automatic conversions. Always prefer constructors over direct instantiation:
//!
//! ```rust
//! use symbolic_mgu::{MguError, SimpleType};
//!
//! // GOOD: Use constructor for SlotsMismatch
//! let err = MguError::from_found_and_expected_unsigned(3usize, 2usize);
//!
//! // AVOID: Direct instantiation (less maintainable)
//! // let err = MguError::SlotsMismatch(3, 2);
//!
//! // GOOD: Use constructor for IndexOutOfRange
//! let err = MguError::from_type_index_and_len(SimpleType::Boolean, 5usize, 3usize);
//!
//! // GOOD: Use constructor for ChildIndexOutOfRange (no type info)
//! let err = MguError::from_index_and_len(5usize, 3usize);
//! ```
//!
//! ## Structured Error Variants
//!
//! For common error patterns, use the structured variants with specific fields rather
//! than string-based variants. These provide better introspection and type safety:
//!
//! ```rust
//! use symbolic_mgu::MguError;
//!
//! // GOOD: Structured variant with typed fields
//! let err = MguError::TermKindMismatch {
//!     expected: "metavariable",
//!     found: "node",
//! };
//!
//! // GOOD: Structured variant for Boolean errors
//! let err = MguError::InvalidBooleanCode {
//!     code: 0xFF,
//!     arity: 2,
//! };
//!
//! // GOOD: Feature requirements
//! let err = MguError::FeatureRequired {
//!     feature: "bigint",
//!     reason: "Boolean codes > 0xFF require bigint feature".to_string(),
//! };
//! ```
//!
//! ## String-Based Variants
//!
//! For domain-specific errors without a dedicated variant, use the appropriate
//! string-based variant:
//!
//! ```rust
//! use symbolic_mgu::MguError;
//!
//! // Use ArgumentError for invalid arguments
//! let err = MguError::ArgumentError("Expected positive value".to_string());
//!
//! // Use UnificationFailure for unification-specific failures
//! let err = MguError::UnificationFailure("Cannot unify x with f(x)".to_string());
//!
//! // Use VerificationFailure for proof verification
//! let err = MguError::VerificationFailure("Proof step invalid".to_string());
//! ```
//!
//! ## I/O and Parsing Errors
//!
//! For file I/O, network operations, and database parsing, use the I/O variants:
//!
//! ```rust
//! use symbolic_mgu::MguError;
//! use std::io;
//!
//! // IoError automatically converts from std::io::Error
//! let io_err = io::Error::new(io::ErrorKind::NotFound, "database.mm");
//! let err: MguError = io_err.into();
//!
//! // ParseError for syntax errors in database files
//! let err = MguError::ParseError {
//!     location: "set.mm:42:15".to_string(),
//!     message: "Unexpected token".to_string(),
//! };
//! ```
//!
//! ## Available Constructors
//!
//! - [`from_type_and_var_strings`](MguError::from_type_and_var_strings) - For `UnknownMetavariable`
//! - [`from_found_and_expected_types`](MguError::from_found_and_expected_types) - For `TypeMismatch` / `TypeUnassignable`
//! - [`from_found_and_expected_unsigned`](MguError::from_found_and_expected_unsigned) - For `SlotsMismatch`
//! - [`from_index_and_len`](MguError::from_index_and_len) - For `ChildIndexOutOfRange`
//! - [`from_type_index_and_len`](MguError::from_type_index_and_len) - For `IndexOutOfRange` with type info
//! - [`from_value_out_of_range_signed`](MguError::from_value_out_of_range_signed) - For signed range errors
//! - [`from_value_out_of_range_unsigned`](MguError::from_value_out_of_range_unsigned) - For unsigned range errors
//! - [`from_unsuported_value_for_type_unsigned`](MguError::from_unsuported_value_for_type_unsigned) - For unsupported values
//! - [`from_illegal_pair`](MguError::from_illegal_pair) - For `PairValidationFailure`
//!
//! ## Error Introspection
//!
//! All error variants can be introspected using accessor methods:
//!
//! ```rust
//! use symbolic_mgu::MguError;
//!
//! let err = MguError::from_index_and_len(5usize, 3usize);
//! assert_eq!(err.get_unwanted_index(), Some(5));
//! assert_eq!(err.get_collection_size(), Some(3));
//! ```

use crate::{MguErrorType, Type, TypeCore};
use std::convert::Infallible;
use std::hash::Hash;
use std::mem::discriminant;
use std::ptr::addr_eq;
use std::rc::Rc;
use thiserror::Error;

/// The common error type of the entire crate.
///
/// # Questions and Answers
///
/// > If a unification fails in CONTRACT or APPLY, the caller handles
/// > the error.  Do you define failure types (e.g. “distinctness
/// > conflict”, “type mismatch”, “no MGU”) separately, or just use
/// > a binary success/failure signal?  Could fine-grained error
/// > types improve diagnostics or debugging?
///
/// If we write this in Rust, we will definitely want fine-grained
/// error types for debugging, as we are completely dependent on
/// user choice of which STATEMENTS to supply as axioms to determine
/// the legality of CONTRACT and APPLY.
#[derive(Error, Clone, Debug)]
pub enum MguError {
    /// Metavariable could not be created.
    #[error("Unknown Metavariable of type {0}: {1}.")]
    UnknownMetavariable(&'static str, String), // type_name, var_info

    /// Type mismatch
    #[error("Type mismatch. {0} was not the expected {1}.")]
    TypeMismatch(Rc<Box<dyn TypeCore>>, Rc<Box<dyn TypeCore>>), // found_type, expected_type

    /// Slots mismatch.
    #[error("Slots mismatch. {0} children supplied to a node with {1} slots.")]
    SlotsMismatch(usize, usize), // n_children, n_slots

    /// Type mismatch
    #[error("Type mismatch. A tree of type {0} cannot be assigned to a slot of type {1}.")]
    TypeUnassignable(Rc<Box<dyn TypeCore>>, Rc<Box<dyn TypeCore>>), // tree_type, slot_or_var_type

    /// Indexed item could not be found.
    #[error("For type {0:?}, index {1} >= available options {2}.")]
    IndexOutOfRange(Rc<Box<dyn TypeCore>>, usize, usize), // the_type, index, n_options

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

    /// Argument Error with descriptive message.
    #[error("Argument error: {0}")]
    ArgumentError(String),

    /// Verification failure with descriptive message.
    #[error("Verification failed: {0}")]
    VerificationFailure(String), // msg

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

    /// Expected a metavariable but found a node, or vice versa.
    #[error("Expected term to be a {expected}, but it is a {found}")]
    TermKindMismatch {
        /// The expected term kind ("metavariable" or "node").
        expected: &'static str,
        /// The actual term kind found.
        found: &'static str,
    },

    /// Node is not a Boolean operation.
    #[error("Node {node_display} is not a Boolean operation")]
    NodeNotBooleanOp {
        /// Display representation of the node.
        node_display: String,
    },

    /// Invalid Boolean function code for the given arity.
    #[error("Invalid Boolean code {code:#x} for arity {arity}")]
    InvalidBooleanCode {
        /// The Boolean function code.
        code: u128,
        /// The arity (number of arguments).
        arity: u8,
    },

    /// Boolean operation arity not supported.
    #[error("Boolean arity {arity} not supported (must be 0-3)")]
    UnsupportedBooleanArity {
        /// The unsupported arity.
        arity: usize,
    },

    /// Boolean evaluation failed (returned `None` or we couldn't compute).
    #[error("Boolean evaluation failed: {reason}")]
    BooleanEvaluationFailed {
        /// Reason for the failure.
        reason: String,
    },

    /// Variable not found in the binding list.
    #[error("Variable {variable} not found in binding list")]
    VariableNotBound {
        /// Display representation of the variable.
        variable: String,
    },

    /// Variable index exceeds the allowed limit.
    #[error("Variable index {index} exceeds limit {limit}")]
    VariableIndexOutOfRange {
        /// The variable index that was out of range.
        index: usize,
        /// The maximum allowed index.
        limit: usize,
    },

    /// Unknown node name in factory method.
    #[error("Unknown node name: {name}")]
    UnknownNodeName {
        /// The unrecognized node name.
        name: String,
    },

    /// Node type doesn't match expected type.
    #[error("Node has type {found}, expected {expected}")]
    NodeTypeMismatch {
        /// The actual node type found.
        found: String,
        /// The expected node type.
        expected: String,
    },

    /// Required feature not enabled.
    #[error("Feature '{feature}' required: {reason}")]
    FeatureRequired {
        /// The name of the required feature (e.g., `"bigint"`).
        feature: &'static str,
        /// Explanation of why the feature is needed.
        reason: String,
    },

    /// Type doesn't support the required capability.
    #[error("Type does not support {capability} capability")]
    TypeCapabilityUnsupported {
        /// The capability name ("Boolean", "Setvar", or "Class").
        capability: &'static str,
    },

    /// Bit position out of range for truth table.
    #[error("Bit position {position} out of range for {bits}-bit value")]
    BitPositionOutOfRange {
        /// The bit position that was out of range.
        position: u64,
        /// The total number of bits available.
        bits: usize,
    },

    /// I/O error from file or network operations.
    ///
    /// This variant wraps errors from `std::io::Error` and similar I/O-related
    /// failures. Use this for file reading/writing, network operations, and
    /// other I/O that may fail.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::MguError;
    /// use std::io;
    ///
    /// // Automatic conversion from std::io::Error
    /// let io_err = io::Error::new(io::ErrorKind::NotFound, "file.mm not found");
    /// let mgu_err: MguError = io_err.into();
    /// assert!(mgu_err.to_string().contains("file.mm"));
    /// ```
    #[error("I/O error: {0}")]
    IoError(String),

    /// Parse error in database file or data stream.
    ///
    /// Use this for syntax errors, invalid tokens, malformed data, or other
    /// parsing failures when reading database files (e.g., Metamath `.mm` files).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::MguError;
    ///
    /// let err = MguError::ParseError {
    ///     location: "set.mm:42:15".to_string(),
    ///     message: "Expected $a, found $p".to_string(),
    /// };
    /// assert!(err.to_string().contains("set.mm:42:15"));
    /// ```
    #[error("Parse error at {location}: {message}")]
    ParseError {
        /// Location in file (e.g., "file.mm:line:col" or byte offset).
        location: String,
        /// Detailed error message describing what went wrong.
        message: String,
    },

    /// Catch-all for bare errors created incorrectly.
    #[error("Error: {0:?}")]
    UnknownErrorType(MguErrorType), // err_type

    /// Catch-all error with message.
    #[error("Error: {0:?}, Message: {1}")]
    UnknownErrorTypeMessage(MguErrorType, String), // err_type, msg

    /// Catch-all error (deprecated - use specific error types instead).
    #[error("Unknown Error with code = {0}.")]
    UnknownError(usize), // code
}

impl MguError {
    /// Constructor.
    #[must_use]
    pub fn from_type_and_var_strings<'a, S>(the_type: &'static str, metavariable: S) -> MguError
    where
        S: Into<&'a str>,
    {
        MguError::UnknownMetavariable(the_type, metavariable.into().to_owned())
    }

    /// Constructor.
    #[must_use]
    pub fn from_found_and_expected_types<T: Type>(
        found_type_is_tree: bool,
        found: &T,
        receiver: &T,
    ) -> MguError {
        if found_type_is_tree {
            if addr_eq(found, receiver) {
                let box0 = Rc::new(found.to_boxed());
                MguError::TypeUnassignable(box0.clone(), box0.clone())
            } else {
                let box1 = Rc::new(found.to_boxed());
                let box2 = Rc::new(found.to_boxed());
                MguError::TypeUnassignable(box1, box2)
            }
        } else if addr_eq(found, receiver) {
            let box0 = Rc::new(found.to_boxed());
            MguError::TypeMismatch(box0.clone(), box0.clone())
        } else {
            let box1 = Rc::new(found.to_boxed());
            let box2 = Rc::new(found.to_boxed());
            MguError::TypeMismatch(box1, box2)
        }
    }

    /// Constructor.
    #[must_use]
    pub fn from_found_and_expected_unsigned<U, V>(found: U, expected: V) -> MguError
    where
        U: Into<usize>,
        V: Into<usize>,
    {
        MguError::SlotsMismatch(found.into(), expected.into())
    }

    /// Constructor for `ChildIndexOutOfRange` (no type information).
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::MguError;
    ///
    /// let err = MguError::from_index_and_len(5usize, 3usize);
    /// assert_eq!(err.get_unwanted_index(), Some(5));
    /// assert_eq!(err.get_collection_size(), Some(3));
    /// ```
    #[must_use]
    pub fn from_index_and_len<U, V>(index: U, length: V) -> MguError
    where
        U: Into<usize>,
        V: Into<usize>,
    {
        MguError::ChildIndexOutOfRange(index.into(), length.into())
    }

    /// Constructor for `IndexOutOfRange` (with type information).
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{MguError, SimpleType};
    ///
    /// let err = MguError::from_type_index_and_len(SimpleType::Boolean, 5usize, 3usize);
    /// assert_eq!(err.get_unwanted_index(), Some(5));
    /// assert_eq!(err.get_collection_size(), Some(3));
    /// ```
    #[must_use]
    pub fn from_type_index_and_len<T, U, V>(for_type: T, index: U, length: V) -> MguError
    where
        T: Type,
        U: Into<usize>,
        V: Into<usize>,
    {
        MguError::IndexOutOfRange(Rc::new(for_type.to_boxed()), index.into(), length.into())
    }

    /// Constructor.
    #[must_use]
    pub fn from_value_out_of_range_signed<U, V, W>(
        value: U,
        dest_type: &'static str,
        min: V,
        max: W,
    ) -> MguError
    where
        U: Into<i128>,
        V: Into<u32>,
        W: Into<u32>,
    {
        MguError::SignedValueOutOfRange(value.into(), dest_type, min.into(), max.into())
    }

    /// Constructor.
    #[must_use]
    pub fn from_value_out_of_range_unsigned<U, V, W>(
        value: U,
        dest_type: &'static str,
        min: V,
        max: W,
    ) -> MguError
    where
        U: Into<u128>,
        V: Into<u32>,
        W: Into<u32>,
    {
        MguError::UnsignedValueOutOfRange(value.into(), dest_type, min.into(), max.into())
    }

    /// Constructor.
    #[must_use]
    pub fn from_unsuported_value_for_type_unsigned<U>(value: U, the_type: &'static str) -> MguError
    where
        U: Into<u128>,
    {
        MguError::UnsignedValueUnsupported(value.into(), the_type)
    }

    /// Constructor.
    #[must_use]
    pub fn from_illegal_pair<'a, S, T>(element1: S, element2: T) -> MguError
    where
        S: Into<&'a str>,
        T: Into<&'a str>,
    {
        MguError::PairValidationFailure(element1.into().to_owned(), element2.into().to_owned())
    }

    /// Constructor.
    #[must_use]
    pub fn from_err_type_and_message<'a, S>(err_type: MguErrorType, msg: S) -> MguError
    where
        S: Into<&'a str>,
    {
        match err_type {
            MguErrorType::UnificationFailure => MguError::UnificationFailure(msg.into().to_owned()),
            MguErrorType::ArgumentError => MguError::ArgumentError(msg.into().to_owned()),
            MguErrorType::VerificationFailure => {
                MguError::VerificationFailure(msg.into().to_owned())
            }
            MguErrorType::DistinctnessViolation => {
                MguError::DistinctnessViolation(msg.into().to_owned())
            }
            MguErrorType::SubstitutionCycle => MguError::SubstitutionCycle(msg.into().to_owned()),
            MguErrorType::AllocationError => MguError::AllocationError(msg.into().to_owned()),
            MguErrorType::NumericConversionError => {
                MguError::NumericConversionError(msg.into().to_owned())
            }
            MguErrorType::ColorParseError => MguError::ColorParseError(msg.into().to_owned()),
            _ => {
                // TODO: log warning.
                MguError::UnknownErrorTypeMessage(err_type, msg.into().to_owned())
            }
        }
    }

    /// Constructor.
    #[must_use]
    pub fn from_bare_err_type_and_message(err_type: MguErrorType) -> MguError {
        match err_type {
            MguErrorType::CliqueOrderingError => MguError::CliqueOrderingError,
            MguErrorType::CliqueMinimumSizeError => MguError::CliqueMinimumSizeError,
            MguErrorType::DecompositionValidationError => MguError::DecompositionValidationError,
            _ => {
                // TODO: log warning.
                MguError::UnknownErrorType(err_type)
            }
        }
    }

    /// Constructor.
    #[must_use]
    pub fn from_error_code<U>(code: U) -> MguError
    where
        U: Into<usize>,
    {
        MguError::UnknownError(code.into())
    }

    /// Get the error type to provide introspection.
    #[must_use]
    pub fn get_error_type(&self) -> MguErrorType {
        match self {
            MguError::UnknownMetavariable(_, _) => MguErrorType::UnknownMetavariable,
            MguError::TypeMismatch(_, _) => MguErrorType::TypeMismatch,
            MguError::SlotsMismatch(_, _) => MguErrorType::SlotsMismatch,
            MguError::TypeUnassignable(_, _) => MguErrorType::TypeUnassignable,
            MguError::IndexOutOfRange(_, _, _) => MguErrorType::IndexOutOfRange,
            MguError::ChildIndexOutOfRange(_, _) => MguErrorType::ChildIndexOutOfRange,
            MguError::SignedValueOutOfRange(_, _, _, _) => MguErrorType::SignedValueOutOfRange,
            MguError::UnsignedValueOutOfRange(_, _, _, _) => MguErrorType::UnsignedValueOutOfRange,
            MguError::UnsignedValueUnsupported(_, _) => MguErrorType::UnsignedValueUnsupported,
            MguError::PairValidationFailure(_, _) => MguErrorType::PairValidationFailure,
            MguError::UnificationFailure(_) => MguErrorType::UnificationFailure,
            MguError::ArgumentError(_) => MguErrorType::ArgumentError,
            MguError::VerificationFailure(_) => MguErrorType::VerificationFailure,
            MguError::DistinctnessViolation(_) => MguErrorType::DistinctnessViolation,
            MguError::SubstitutionCycle(_) => MguErrorType::SubstitutionCycle,
            MguError::CliqueOrderingError => MguErrorType::CliqueOrderingError,
            MguError::CliqueMinimumSizeError => MguErrorType::CliqueMinimumSizeError,
            MguError::DecompositionValidationError => MguErrorType::DecompositionValidationError,
            MguError::AllocationError(_) => MguErrorType::AllocationError,
            MguError::NumericConversionError(_) => MguErrorType::NumericConversionError,
            MguError::ColorParseError(_) => MguErrorType::ColorParseError,
            MguError::TermKindMismatch { .. } => MguErrorType::TermKindMismatch,
            MguError::NodeNotBooleanOp { .. } => MguErrorType::NodeNotBooleanOp,
            MguError::InvalidBooleanCode { .. } => MguErrorType::InvalidBooleanCode,
            MguError::UnsupportedBooleanArity { .. } => MguErrorType::UnsupportedBooleanArity,
            MguError::BooleanEvaluationFailed { .. } => MguErrorType::BooleanEvaluationFailed,
            MguError::VariableNotBound { .. } => MguErrorType::VariableNotBound,
            MguError::VariableIndexOutOfRange { .. } => MguErrorType::VariableIndexOutOfRange,
            MguError::UnknownNodeName { .. } => MguErrorType::UnknownNodeName,
            MguError::NodeTypeMismatch { .. } => MguErrorType::NodeTypeMismatch,
            MguError::FeatureRequired { .. } => MguErrorType::FeatureRequired,
            MguError::TypeCapabilityUnsupported { .. } => MguErrorType::TypeCapabilityUnsupported,
            MguError::BitPositionOutOfRange { .. } => MguErrorType::BitPositionOutOfRange,
            MguError::IoError(_) => MguErrorType::IoError,
            MguError::ParseError { .. } => MguErrorType::ParseError,
            MguError::UnknownErrorType(_) => MguErrorType::UnknownErrorType,
            MguError::UnknownErrorTypeMessage(_, _) => MguErrorType::UnknownErrorTypeMessage,
            MguError::UnknownError(_) => MguErrorType::UnknownError,
        }
    }

    /// Get the destination type string if this is a `UnknownMetavariable`, `SignedValueOutOfRange`, `UnsignedValueOutOfRange`, or `UnsignedValueUnsupported` instance.
    #[must_use]
    pub fn get_type_name(&self) -> Option<&'static str> {
        match self {
            MguError::UnknownMetavariable(a_type, _)
            | MguError::SignedValueOutOfRange(_, a_type, _, _)
            | MguError::UnsignedValueOutOfRange(_, a_type, _, _)
            | MguError::UnsignedValueUnsupported(_, a_type) => Some(*a_type),
            _ => None,
        }
    }

    /// Get the name of the variable if this is an `UnknownMetavariable` instance.
    #[must_use]
    pub fn get_var_info(&self) -> Option<String> {
        if let MguError::UnknownMetavariable(_, value) = self {
            Some((*value).clone())
        } else {
            None
        }
    }

    /// Get the unwanted found type if this is a `TypeMismatch` or `TypeUnassignable` instance.
    #[must_use]
    pub fn get_unwanted_found_type(&self) -> Option<Rc<Box<dyn TypeCore>>> {
        match self {
            MguError::TypeMismatch(value, _) | MguError::TypeUnassignable(value, _) => {
                Some(value.clone())
            }
            _ => None,
        }
    }

    /// Get the type of the receiver if this is a `TypeMismatch`, `TypeUnassignable` or `IndexOutOfRange` instance.
    #[must_use]
    pub fn get_receiver_type(&self) -> Option<Rc<Box<dyn TypeCore>>> {
        match self {
            MguError::TypeMismatch(_, value)
            | MguError::TypeUnassignable(_, value)
            | MguError::IndexOutOfRange(value, _, _) => Some(value.clone()),
            _ => None,
        }
    }

    /// Get the unwanted found `usize` if this is a `SlotsMismatch` instance.
    #[must_use]
    pub fn get_unwanted_found_usize(&self) -> Option<usize> {
        match self {
            MguError::SlotsMismatch(value, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the type of the receiver if is this is a `SlotsMismatch` instance.
    #[must_use]
    pub fn get_expected_usize(&self) -> Option<usize> {
        match self {
            MguError::SlotsMismatch(_, value) => Some(*value),
            _ => None,
        }
    }

    /// Get the unwanted index if this is an `IndexOutOfRange` or `ChildIndexOutOfRange` instance.
    #[must_use]
    pub fn get_unwanted_index(&self) -> Option<usize> {
        match self {
            MguError::IndexOutOfRange(_, index, _) | MguError::ChildIndexOutOfRange(index, _) => {
                Some(*index)
            }
            _ => None,
        }
    }

    /// Get the collection size if this is an `IndexOutOfRange` or `ChildIndexOutOfRange` instance.
    #[must_use]
    pub fn get_collection_size(&self) -> Option<usize> {
        match self {
            MguError::IndexOutOfRange(_, _, size) | MguError::ChildIndexOutOfRange(_, size) => {
                Some(*size)
            }
            _ => None,
        }
    }

    /// Get the unwanted value if this is a `SignedValueOutOfRange` instance.
    #[must_use]
    pub fn get_unwanted_value_signed(&self) -> Option<i128> {
        match self {
            MguError::SignedValueOutOfRange(value, _, _, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the unwanted value if this is an `UnsignedValueOutOfRange`, or `UnsignedValueUnsupported` instance.
    #[must_use]
    pub fn get_unwanted_value_unsigned(&self) -> Option<u128> {
        match self {
            MguError::UnsignedValueOutOfRange(value, _, _, _)
            | MguError::UnsignedValueUnsupported(value, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the minimum of the allowable range if this is a `SignedValueOutOfRange` or `UnsignedValueOutOfRange` instance.
    #[must_use]
    pub fn get_minimum_allowed(&self) -> Option<u32> {
        match self {
            MguError::SignedValueOutOfRange(_, _, min, _)
            | MguError::UnsignedValueOutOfRange(_, _, min, _) => Some(*min),
            _ => None,
        }
    }

    /// Get the maximum of the allowable range if this is a `SignedValueOutOfRange` or `UnsignedValueOutOfRange` instance.
    #[must_use]
    pub fn get_maximum_allowed(&self) -> Option<u32> {
        match self {
            MguError::SignedValueOutOfRange(_, _, _, max)
            | MguError::UnsignedValueOutOfRange(_, _, _, max) => Some(*max),
            _ => None,
        }
    }

    /// Get element on left of an illegal pair if this is a `PairValidationFailure` instance.
    #[must_use]
    pub fn get_illegal_pair_left_element(&self) -> Option<String> {
        match self {
            MguError::PairValidationFailure(left, _) => Some(left.to_owned()),
            _ => None,
        }
    }

    /// Get element on right of an illegal pair if this is a `PairValidationFailure` instance.
    #[must_use]
    pub fn get_illegal_pair_right_element(&self) -> Option<String> {
        match self {
            MguError::PairValidationFailure(_, right) => Some(right.to_owned()),
            _ => None,
        }
    }

    /// Get payload error type of an incorrectly constructed instance of `UnknownErrorTypeMessage` or `UnknownErrorType`.
    #[must_use]
    pub fn get_payload_error_type(&self) -> Option<MguErrorType> {
        match self {
            MguError::UnknownErrorTypeMessage(the_type, _)
            | MguError::UnknownErrorType(the_type) => Some(*the_type),
            _ => None,
        }
    }

    /// Get payload error code of an `UnknownError` instance.
    #[must_use]
    pub fn get_code(&self) -> Option<usize> {
        match self {
            MguError::UnknownError(code) => Some(*code),
            _ => None,
        }
    }
}

impl PartialEq for MguError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::UnknownMetavariable(l0, l1), Self::UnknownMetavariable(r0, r1)) => {
                l0 == r0 && l1 == r1
            }
            (Self::TypeMismatch(l0, l1), Self::TypeMismatch(r0, r1)) => {
                if Rc::ptr_eq(l0, r0) && Rc::ptr_eq(l1, r1) {
                    return true;
                }
                l0.to_string() == r0.to_string() && l1.to_string() == r1.to_string()
            }
            (Self::SlotsMismatch(l0, l1), Self::SlotsMismatch(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::TypeUnassignable(l0, l1), Self::TypeUnassignable(r0, r1)) => {
                if Rc::ptr_eq(l0, r0) && Rc::ptr_eq(l1, r1) {
                    return true;
                }
                l0.to_string() == r0.to_string() && l1.to_string() == r1.to_string()
            }
            (Self::IndexOutOfRange(l0, l1, l2), Self::IndexOutOfRange(r0, r1, r2)) => {
                if Rc::ptr_eq(l0, r0) && l1 == r1 && l2 == r2 {
                    return true;
                }
                l0.to_string() == r0.to_string() && l1 == r1 && l2 == r2
            }
            (Self::ChildIndexOutOfRange(l0, l1), Self::ChildIndexOutOfRange(r0, r1)) => {
                l0 == r0 && l1 == r1
            }
            (
                Self::SignedValueOutOfRange(l0, l1, l2, l3),
                Self::SignedValueOutOfRange(r0, r1, r2, r3),
            ) => l0 == r0 && l1 == r1 && l2 == r2 && l3 == r3,
            (
                Self::UnsignedValueOutOfRange(l0, l1, l2, l3),
                Self::UnsignedValueOutOfRange(r0, r1, r2, r3),
            ) => l0 == r0 && l1 == r1 && l2 == r2 && l3 == r3,
            (Self::UnsignedValueUnsupported(l0, l1), Self::UnsignedValueUnsupported(r0, r1)) => {
                l0 == r0 && l1 == r1
            }
            (Self::PairValidationFailure(l0, l1), Self::PairValidationFailure(r0, r1)) => {
                l0 == r0 && l1 == r1
            }
            (Self::UnificationFailure(l0), Self::UnificationFailure(r0)) => l0 == r0,
            (Self::ArgumentError(l0), Self::ArgumentError(r0)) => l0 == r0,
            (Self::VerificationFailure(l0), Self::VerificationFailure(r0)) => l0 == r0,
            (Self::DistinctnessViolation(l0), Self::DistinctnessViolation(r0)) => l0 == r0,
            (Self::SubstitutionCycle(l0), Self::SubstitutionCycle(r0)) => l0 == r0,
            (Self::AllocationError(l0), Self::AllocationError(r0)) => l0 == r0,
            (Self::NumericConversionError(l0), Self::NumericConversionError(r0)) => l0 == r0,
            (Self::ColorParseError(l0), Self::ColorParseError(r0)) => l0 == r0,
            (
                Self::TermKindMismatch {
                    expected: l_exp,
                    found: l_found,
                },
                Self::TermKindMismatch {
                    expected: r_exp,
                    found: r_found,
                },
            ) => l_exp == r_exp && l_found == r_found,
            (
                Self::NodeNotBooleanOp { node_display: l0 },
                Self::NodeNotBooleanOp { node_display: r0 },
            ) => l0 == r0,
            (
                Self::InvalidBooleanCode {
                    code: l_code,
                    arity: l_arity,
                },
                Self::InvalidBooleanCode {
                    code: r_code,
                    arity: r_arity,
                },
            ) => l_code == r_code && l_arity == r_arity,
            (
                Self::UnsupportedBooleanArity { arity: l0 },
                Self::UnsupportedBooleanArity { arity: r0 },
            ) => l0 == r0,
            (
                Self::BooleanEvaluationFailed { reason: l0 },
                Self::BooleanEvaluationFailed { reason: r0 },
            ) => l0 == r0,
            (Self::VariableNotBound { variable: l0 }, Self::VariableNotBound { variable: r0 }) => {
                l0 == r0
            }
            (
                Self::VariableIndexOutOfRange {
                    index: l_idx,
                    limit: l_lim,
                },
                Self::VariableIndexOutOfRange {
                    index: r_idx,
                    limit: r_lim,
                },
            ) => l_idx == r_idx && l_lim == r_lim,
            (Self::UnknownNodeName { name: l0 }, Self::UnknownNodeName { name: r0 }) => l0 == r0,
            (
                Self::NodeTypeMismatch {
                    found: l_found,
                    expected: l_exp,
                },
                Self::NodeTypeMismatch {
                    found: r_found,
                    expected: r_exp,
                },
            ) => l_found == r_found && l_exp == r_exp,
            (
                Self::FeatureRequired {
                    feature: l_feat,
                    reason: l_reason,
                },
                Self::FeatureRequired {
                    feature: r_feat,
                    reason: r_reason,
                },
            ) => l_feat == r_feat && l_reason == r_reason,
            (
                Self::TypeCapabilityUnsupported { capability: l0 },
                Self::TypeCapabilityUnsupported { capability: r0 },
            ) => l0 == r0,
            (
                Self::BitPositionOutOfRange {
                    position: l_pos,
                    bits: l_bits,
                },
                Self::BitPositionOutOfRange {
                    position: r_pos,
                    bits: r_bits,
                },
            ) => l_pos == r_pos && l_bits == r_bits,
            (Self::UnknownErrorType(l0), Self::UnknownErrorType(r0)) => l0 == r0,
            (Self::UnknownErrorTypeMessage(l0, l1), Self::UnknownErrorTypeMessage(r0, r1)) => {
                l0 == r0 && l1 == r1
            }
            (Self::UnknownError(l0), Self::UnknownError(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Eq for MguError {}

/// Convert from Infallible (which can never be constructed).
///
/// This impl exists to satisfy trait bounds like `Error: Into<MguError>` when
/// `Error = Infallible`. Since `Infallible` can never be instantiated, this
/// method can never actually be called.
impl From<Infallible> for MguError {
    fn from(x: Infallible) -> Self {
        match x {}
    }
}

/// Automatic conversion from `std::io::Error` to `MguError`.
///
/// This enables the `?` operator to work seamlessly when reading files or
/// performing other I/O operations in functions that return `Result<T, MguError>`.
///
/// # Examples
///
/// ```rust
/// use symbolic_mgu::MguError;
/// use std::fs::File;
/// use std::io::Read;
///
/// fn read_database(path: &str) -> Result<String, MguError> {
///     let mut file = File::open(path)?;  // Automatic conversion
///     let mut contents = String::new();
///     file.read_to_string(&mut contents)?;  // Automatic conversion
///     Ok(contents)
/// }
/// ```
impl From<std::io::Error> for MguError {
    fn from(err: std::io::Error) -> Self {
        MguError::IoError(err.to_string())
    }
}

impl Hash for MguError {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        match self {
            MguError::UnknownMetavariable(a, b) => {
                (*a).hash(state);
                b.hash(state);
            }
            MguError::TypeMismatch(type_core0, type_core1) => {
                Rc::as_ptr(&(type_core0.clone())).hash(state);
                Rc::as_ptr(&(type_core1.clone())).hash(state);
            }
            MguError::SlotsMismatch(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            MguError::TypeUnassignable(type_core0, type_core1) => {
                Rc::as_ptr(&(type_core0.clone())).hash(state);
                Rc::as_ptr(&(type_core1.clone())).hash(state);
            }
            MguError::IndexOutOfRange(type_core, a, b) => {
                Rc::as_ptr(&(type_core.clone())).hash(state);
                a.hash(state);
                b.hash(state);
            }
            MguError::ChildIndexOutOfRange(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            MguError::SignedValueOutOfRange(a, b, c, d) => {
                a.hash(state);
                (*b).hash(state);
                c.hash(state);
                d.hash(state);
            }
            MguError::UnsignedValueOutOfRange(a, b, c, d) => {
                a.hash(state);
                (*b).hash(state);
                c.hash(state);
                d.hash(state);
            }
            MguError::UnsignedValueUnsupported(a, b) => {
                a.hash(state);
                (*b).hash(state);
            }
            MguError::PairValidationFailure(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            MguError::UnificationFailure(msg)
            | MguError::ArgumentError(msg)
            | MguError::VerificationFailure(msg)
            | MguError::DistinctnessViolation(msg)
            | MguError::SubstitutionCycle(msg)
            | MguError::AllocationError(msg)
            | MguError::NumericConversionError(msg)
            | MguError::ColorParseError(msg) => {
                msg.hash(state);
            }
            MguError::CliqueOrderingError
            | MguError::CliqueMinimumSizeError
            | MguError::DecompositionValidationError => {}
            MguError::TermKindMismatch { expected, found } => {
                (*expected).hash(state);
                (*found).hash(state);
            }
            MguError::NodeNotBooleanOp { node_display } => {
                node_display.hash(state);
            }
            MguError::InvalidBooleanCode { code, arity } => {
                code.hash(state);
                arity.hash(state);
            }
            MguError::UnsupportedBooleanArity { arity } => {
                arity.hash(state);
            }
            MguError::BooleanEvaluationFailed { reason } => {
                reason.hash(state);
            }
            MguError::VariableNotBound { variable } => {
                variable.hash(state);
            }
            MguError::VariableIndexOutOfRange { index, limit } => {
                index.hash(state);
                limit.hash(state);
            }
            MguError::UnknownNodeName { name } => {
                name.hash(state);
            }
            MguError::NodeTypeMismatch { found, expected } => {
                found.hash(state);
                expected.hash(state);
            }
            MguError::FeatureRequired { feature, reason } => {
                (*feature).hash(state);
                reason.hash(state);
            }
            MguError::TypeCapabilityUnsupported { capability } => {
                (*capability).hash(state);
            }
            MguError::BitPositionOutOfRange { position, bits } => {
                position.hash(state);
                bits.hash(state);
            }
            MguError::IoError(s) => {
                s.hash(state);
            }
            MguError::ParseError { location, message } => {
                location.hash(state);
                message.hash(state);
            }
            MguError::UnknownErrorType(mgu_error_type) => {
                mgu_error_type.hash(state);
            }
            MguError::UnknownErrorTypeMessage(mgu_error_type, _) => {
                mgu_error_type.hash(state);
            }
            MguError::UnknownError(code) => {
                code.hash(state);
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn unknown_error() {
        let code: u16 = 1859;

        // Test constructor.
        let x1 = MguError::UnknownError(code as usize);
        let x2 = MguError::from_error_code(code);
        assert_eq!(x1, x2);

        // Test accessor methods
        assert_eq!(x1.get_code(), Some(code as usize));
        assert_eq!(x1.get_collection_size(), None);
        assert_eq!(x1.get_error_type(), MguErrorType::UnknownError);
        assert_eq!(x1.get_expected_usize(), None);
        assert_eq!(x1.get_illegal_pair_left_element(), None);
        assert_eq!(x1.get_illegal_pair_right_element(), None);
        assert_eq!(x1.get_maximum_allowed(), None);
        assert_eq!(x1.get_minimum_allowed(), None);
        assert_eq!(x1.get_payload_error_type(), None);
        assert!(x1.get_receiver_type().is_none());
        assert_eq!(x1.get_type_name(), None);
        assert!(x1.get_unwanted_found_type().is_none());
        assert_eq!(x1.get_unwanted_found_usize(), None);
        assert_eq!(x1.get_unwanted_index(), None);
        assert_eq!(x1.get_unwanted_value_signed(), None);
        assert_eq!(x1.get_unwanted_value_unsigned(), None);
        assert_eq!(x1.get_var_info(), None);

        // Test Display format.
        let s = format!("{x1}");
        assert_eq!(s, "Unknown Error with code = 1859.".to_owned());

        // Test Debug format.
        let s = format!("{x1:?}");
        assert_eq!(s, "UnknownError(1859)".to_owned());
    }
}
