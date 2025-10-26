//! Common error handling via enum.

use crate::{MguErrorType, Type};
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
#[derive(Error, Clone, Debug, PartialEq, Eq, Hash)]
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
    pub fn from_type_and_var_strings<'a, S>(the_type: &'static str, metavariable: S) -> MguError
    where
        S: Into<&'a str>,
    {
        MguError::UnknownMetavariable(the_type, metavariable.into().to_owned())
    }

    /// Constructor.
    pub fn from_found_and_expected_types(
        found_type_is_tree: bool,
        found: Type,
        receiver: Type,
    ) -> MguError {
        if found_type_is_tree {
            MguError::TypeUnassignable(found, receiver)
        } else {
            MguError::TypeMismatch(found, receiver)
        }
    }

    /// Constructor.
    pub fn from_found_and_expected_unsigned<U, V>(found: U, expected: V) -> MguError
    where
        U: Into<usize>,
        V: Into<usize>,
    {
        MguError::SlotsMismatch(found.into(), expected.into())
    }

    /// Constructor.
    pub fn from_index_and_len<U, V>(for_type: Option<Type>, index: U, length: V) -> MguError
    where
        U: Into<usize>,
        V: Into<usize>,
    {
        if let Some(the_type) = for_type {
            MguError::IndexOutOfRange(the_type, index.into(), length.into())
        } else {
            MguError::ChildIndexOutOfRange(index.into(), length.into())
        }
    }

    /// Constructor.
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
    pub fn from_unsuported_value_for_type_unsigned<U>(value: U, the_type: &'static str) -> MguError
    where
        U: Into<u128>,
    {
        MguError::UnsignedValueUnsupported(value.into(), the_type)
    }

    /// Constructor.
    pub fn from_illegal_pair<'a, S, T>(element1: S, element2: T) -> MguError
    where
        S: Into<&'a str>,
        T: Into<&'a str>,
    {
        MguError::PairValidationFailure(element1.into().to_owned(), element2.into().to_owned())
    }

    /// Constructor.
    pub fn from_err_type_and_message<'a, S>(err_type: MguErrorType, msg: S) -> MguError
    where
        S: Into<&'a str>,
    {
        match err_type {
            MguErrorType::UnificationFailure => MguError::UnificationFailure(msg.into().to_owned()),
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
    pub fn from_error_code<U>(code: U) -> MguError
    where
        U: Into<usize>,
    {
        MguError::UnknownError(code.into())
    }

    /// Get the error type to provide introspection.
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
            MguError::DistinctnessViolation(_) => MguErrorType::DistinctnessViolation,
            MguError::SubstitutionCycle(_) => MguErrorType::SubstitutionCycle,
            MguError::CliqueOrderingError => MguErrorType::CliqueOrderingError,
            MguError::CliqueMinimumSizeError => MguErrorType::CliqueMinimumSizeError,
            MguError::DecompositionValidationError => MguErrorType::DecompositionValidationError,
            MguError::AllocationError(_) => MguErrorType::AllocationError,
            MguError::NumericConversionError(_) => MguErrorType::NumericConversionError,
            MguError::ColorParseError(_) => MguErrorType::ColorParseError,
            MguError::UnknownErrorType(_) => MguErrorType::UnknownErrorType,
            MguError::UnknownErrorTypeMessage(_, _) => MguErrorType::UnknownErrorTypeMessage,
            MguError::UnknownError(_) => MguErrorType::UnknownError,
        }
    }

    /// Get the destination type string if this is a `UnknownMetavariable`, `SignedValueOutOfRange`, `UnsignedValueOutOfRange`, or `UnsignedValueUnsupported` instance.
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
    pub fn get_var_info(&self) -> Option<String> {
        if let MguError::UnknownMetavariable(_, value) = self {
            Some((*value).clone())
        } else {
            None
        }
    }

    /// Get the unwanted found type if this is a `TypeMismatch` or `TypeUnassignable` instance.
    pub fn get_unwanted_found_type(&self) -> Option<Type> {
        match self {
            MguError::TypeMismatch(value, _) | MguError::TypeUnassignable(value, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the type of the receiver if this is a `TypeMismatch`, `TypeUnassignable` or `IndexOutOfRange` instance.
    pub fn get_receiver_type(&self) -> Option<Type> {
        match self {
            MguError::TypeMismatch(_, value)
            | MguError::TypeUnassignable(_, value)
            | MguError::IndexOutOfRange(value, _, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the unwanted found `usize` if this is a `SlotsMismatch` instance.
    pub fn get_unwanted_found_usize(&self) -> Option<usize> {
        match self {
            MguError::SlotsMismatch(value, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the type of the receiver if is this is a `SlotsMismatch` instance.
    pub fn get_expected_usize(&self) -> Option<usize> {
        match self {
            MguError::SlotsMismatch(_, value) => Some(*value),
            _ => None,
        }
    }

    /// Get the unwanted index if this is an `IndexOutOfRange` or `ChildIndexOutOfRange` instance.
    pub fn get_unwanted_index(&self) -> Option<usize> {
        match self {
            MguError::IndexOutOfRange(_, index, _) | MguError::ChildIndexOutOfRange(index, _) => {
                Some(*index)
            }
            _ => None,
        }
    }

    /// Get the collection size if this is an `IndexOutOfRange` or `ChildIndexOutOfRange` instance.
    pub fn get_collection_size(&self) -> Option<usize> {
        match self {
            MguError::IndexOutOfRange(_, _, size) | MguError::ChildIndexOutOfRange(_, size) => {
                Some(*size)
            }
            _ => None,
        }
    }

    /// Get the unwanted value if this is a `SignedValueOutOfRange` instance.
    pub fn get_unwanted_value_signed(&self) -> Option<i128> {
        match self {
            MguError::SignedValueOutOfRange(value, _, _, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the unwanted value if this is an `UnsignedValueOutOfRange`, or `UnsignedValueUnsupported` instance.
    pub fn get_unwanted_value_unsigned(&self) -> Option<u128> {
        match self {
            MguError::UnsignedValueOutOfRange(value, _, _, _)
            | MguError::UnsignedValueUnsupported(value, _) => Some(*value),
            _ => None,
        }
    }

    /// Get the minimum of the allowable range if this is a `SignedValueOutOfRange` or `UnsignedValueOutOfRange` instance.
    pub fn get_minimum_allowed(&self) -> Option<u32> {
        match self {
            MguError::SignedValueOutOfRange(_, _, min, _)
            | MguError::UnsignedValueOutOfRange(_, _, min, _) => Some(*min),
            _ => None,
        }
    }

    /// Get the maximum of the allowable range if this is a `SignedValueOutOfRange` or `UnsignedValueOutOfRange` instance.
    pub fn get_maximum_allowed(&self) -> Option<u32> {
        match self {
            MguError::SignedValueOutOfRange(_, _, _, max)
            | MguError::UnsignedValueOutOfRange(_, _, _, max) => Some(*max),
            _ => None,
        }
    }

    /// Get element on left of an illegal pair if this is a `PairValidationFailure` instance.
    pub fn get_illegal_pair_left_element(&self) -> Option<String> {
        match self {
            MguError::PairValidationFailure(left, _) => Some(left.to_owned()),
            _ => None,
        }
    }

    /// Get element on right of an illegal pair if this is a `PairValidationFailure` instance.
    pub fn get_illegal_pair_right_element(&self) -> Option<String> {
        match self {
            MguError::PairValidationFailure(_, right) => Some(right.to_owned()),
            _ => None,
        }
    }

    /// Get payload error type of an incorrectly constructed instance of `UnknownErrorTypeMessage` or `UnknownErrorType`.
    pub fn get_payload_error_type(&self) -> Option<MguErrorType> {
        match self {
            MguError::UnknownErrorTypeMessage(the_type, _)
            | MguError::UnknownErrorType(the_type) => Some(*the_type),
            _ => None,
        }
    }

    /// Get payload error code of an `UnknownError` instance.
    pub fn get_code(&self) -> Option<usize> {
        match self {
            MguError::UnknownError(code) => Some(*code),
            _ => None,
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
        assert_eq!(x1.get_receiver_type(), None);
        assert_eq!(x1.get_type_name(), None);
        assert_eq!(x1.get_unwanted_found_type(), None);
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
