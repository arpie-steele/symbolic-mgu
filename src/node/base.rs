//! The top of a [`Term`] is a [`Node`] or the term is a bare
//! [`Metavariable`].
//!
//! [`Metavariable`]: `crate::Metavariable`
//! [`Term`]: `crate::Term`

use crate::{MguError, Type};
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// TODO.
pub trait Node: Debug + Display + PartialEq + Eq + Hash + Clone {
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
    fn get_arity(&self) -> Result<usize, MguError>; // alias: `get_n_slots`()

    /// Return data about this Metavariable sufficient for a compatible factory to recreate it.
    ///
    /// # Errors
    /// - When the index is out-of-range `(0..n)` where `n = self.get_arity()?`
    /// - Typically only when this type requires a Weak reference to a factory object which has gone missing.
    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError>;

    /// Convert this node to a `BooleanSimpleOp` if it represents a Boolean operation.
    ///
    /// Returns `Some(op)` if this node can be evaluated as a Boolean operation,
    /// `None` if the node doesn't represent a Boolean operation (e.g., set operations,
    /// quantifiers, or other non-Boolean nodes).
    ///
    /// This method enables generic Boolean evaluation without requiring conversion
    /// to specific node implementations.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{Node, NodeByte, BooleanSimpleOp};
    ///
    /// let and_node = NodeByte::And;
    /// assert_eq!(and_node.to_boolean_op(), Some(BooleanSimpleOp::AndAB2));
    ///
    /// let not_node = NodeByte::Not;
    /// assert_eq!(not_node.to_boolean_op(), Some(BooleanSimpleOp::NotA1));
    ///
    /// // Non-Boolean operations return None
    /// let element_of = NodeByte::IsElementOf;
    /// assert_eq!(element_of.to_boolean_op(), None);
    /// ```
    fn to_boolean_op(&self) -> Option<crate::BooleanSimpleOp>;
}
