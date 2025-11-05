//! Introduce the [`Metavariable`] trait which has ready-made short
//! and wide toy implementations.

pub(crate) mod enums;
pub(crate) mod factory;
pub(crate) mod meta_byte;
pub(crate) mod wide;
pub(crate) mod wide_factory;

use crate::{MguError, Type};
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Trait encapsulating behavior of the metavariable type.
///
/// Metavariables are typed variables used in logical terms and statements.
/// Each metavariable has a type (Boolean, Setvar, or Class) and an index
/// that distinguishes it from other variables of the same type.
pub trait Metavariable: Display + Debug + Clone + Hash + PartialEq + Eq {
    /// Concrete implementation of the Type trait.
    type Type: Type;

    /// Return data about this Metavariable sufficient for a compatible factory to recreate it.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError>;

    /// Return the Type of this Metavariable.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_type(&self) -> Result<Self::Type, MguError> {
        self.get_type_and_index().map(|x| x.0)
    }

    /// Return the internal index of this Metavariable.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_index(&self) -> Result<usize, MguError> {
        self.get_type_and_index().map(|x| x.1)
    }

    /// Return the maximum index available for the given type.
    ///
    /// For implementations with unlimited variables (like [`WideMetavariable`]),
    /// this returns `usize::MAX`. For limited implementations (like [`MetaByte`]),
    /// this returns the actual maximum index.
    fn max_index_by_type(typ: Self::Type) -> usize;

    /// Try to create a metavariable from a type and index.
    ///
    /// # Errors
    /// - Returns an error if the index exceeds the maximum for this type
    fn try_from_type_and_index(my_type: Self::Type, my_index: usize) -> Result<Self, MguError>;

    /// Enumerate all metavariables of the given type, starting from index 0.
    ///
    /// For implementations with unlimited variables, this iterator is infinite.
    /// For limited implementations, it terminates at the maximum index.
    fn enumerate(for_type: Self::Type) -> impl Iterator<Item = Self>;
}
