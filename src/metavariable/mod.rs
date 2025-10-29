//! Introduce the [`Metavariable`] trait which has ready-made short
//! and wide toy implementations.

pub(crate) mod enums;
pub(crate) mod factory;
pub(crate) mod meta_byte;

use crate::{MguError, Type};
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Trait encapsulating behavior of the metavariable type.
///
/// TODO.
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
}
