//! The top of a [`Term`] is a [`Node`] or the term is a bare
//! [`Metavariable`].
//!
//! [`Metavariable`]: `crate::Metavariable`
//! [`Term`]: `crate::Term`

use crate::{MguError, Type};

/// TODO.
pub trait Node {
    /// Concrete implementation of the Type trait.
    type Type: Type;

    /// Return data about this Metavariable sufficient for a compatible factory to recreate it.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError>;

    /// Return the type of this Node.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_type(&self) -> Result<Self::Type, MguError> {
        self.get_type_and_index().map(|x| x.0)
    }

    /// Return the internal index of this Metavariable.
    ///
    /// This is unrelated to the index into the children of a Term or the slots defined for a Node.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_index(&self) -> Result<usize, MguError> {
        self.get_type_and_index().map(|x| x.1)
    }

    /// Return data about number of slots for this metavariable.
    ///
    /// # Errors
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_arity(&self) -> Result<usize, MguError>;

    /// Return data about this Metavariable sufficient for a compatible factory to recreate it.
    ///
    /// # Errors
    /// - When the index is out-of-range `(0..n)` where `n = self.get_arity()?`
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError>;
}
