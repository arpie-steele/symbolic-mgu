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

    /// Format this node with the given formatter.
    ///
    /// This method allows nodes to customize their representation
    /// based on the formatter being used. Different formatters support
    /// different output formats (ASCII, UTF-8, LaTeX, HTML, etc.).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations should override this to provide
    /// formatter-specific rendering.
    ///
    /// # Arguments
    ///
    /// * `formatter` - The formatter to use for rendering
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use symbolic_mgu::{Node, OutputFormatter, get_formatter};
    ///
    /// let node = /* some node */;
    /// let formatter = get_formatter("utf8-color");
    /// let output = node.format_with(&*formatter);
    /// ```
    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        let _ = formatter; // Suppress unused warning
        format!("{}", self) // Default: use Display
    }

    /// Get ASCII operator symbol for this node.
    ///
    /// This provides a pure ASCII rendering suitable for environments
    /// that don't support Unicode (e.g., Metamath compatibility, plain text).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations (like NodeByte) should override to provide
    /// appropriate ASCII symbols (e.g., "->", "/\\", "\\/").
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use symbolic_mgu::Node;
    ///
    /// let node = /* some node */;
    /// let ascii = node.to_ascii_symbol(); // e.g., "->" for implies
    /// ```
    fn to_ascii_symbol(&self) -> &str {
        "?" // Default: unknown operator
    }

    /// Get UTF-8 operator symbol for this node.
    ///
    /// This provides a Unicode rendering with mathematical symbols
    /// (e.g., →, ∧, ∨, ¬).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations should override to provide appropriate
    /// Unicode symbols.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use symbolic_mgu::Node;
    ///
    /// let node = /* some node */;
    /// let utf8 = node.to_utf8_symbol(); // e.g., "→" for implies
    /// ```
    fn to_utf8_symbol(&self) -> &str {
        "?" // Default: unknown operator
    }

    /// Get LaTeX operator symbol for this node.
    ///
    /// This provides a LaTeX math mode rendering
    /// (e.g., \\to, \\land, \\lor, \\neg).
    ///
    /// # Default Implementation
    ///
    /// Returns a placeholder. Concrete implementations should override
    /// to provide appropriate LaTeX commands.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use symbolic_mgu::Node;
    ///
    /// let node = /* some node */;
    /// let latex = node.to_latex_symbol(); // e.g., "\\to" for implies
    /// ```
    fn to_latex_symbol(&self) -> &str {
        "?" // Default: unknown operator
    }
}
