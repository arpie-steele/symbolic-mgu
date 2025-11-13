//! Introduce the [`Metavariable`] trait which has ready-made short
//! and wide toy implementations.

pub(crate) mod charset;
pub(crate) mod decorator;
pub(crate) mod enums;
pub(crate) mod factory;
pub(crate) mod meta_byte;
pub(crate) mod parametric;
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
///
/// The `Ord` bound is required to support statement canonicalization,
/// which produces a unique minimal representation by ordering variables
/// lexicographically.
pub trait Metavariable: Display + Debug + Clone + Hash + PartialEq + Eq + PartialOrd + Ord {
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
    ///
    /// [`MetaByte`]: `crate::MetaByte`
    /// [`WideMetavariable`]: `crate::WideMetavariable`
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

    /// Format this metavariable with the given formatter.
    ///
    /// This method allows metavariables to customize their representation
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
    /// ```rust
    /// use symbolic_mgu::{Metavariable, MetaByte, SimpleType, get_formatter};
    ///
    /// let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
    /// let formatter = get_formatter("utf8");
    /// let output = var.format_with(&*formatter);
    /// assert_eq!(output, "P");
    /// ```
    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        let _ = formatter; // Suppress unused warning
        format!("{}", self) // Default: use Display
    }

    /// Get ASCII representation of this metavariable.
    ///
    /// This provides a pure ASCII rendering suitable for environments
    /// that don't support Unicode (e.g., Metamath compatibility, plain text).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations (like `MetaByte`) should override to provide
    /// appropriate ASCII names (e.g., "ph", "ps", "ch").
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Metavariable, MetaByte, SimpleType};
    ///
    /// let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
    /// let ascii = var.to_ascii();
    /// assert_eq!(ascii, "ph"); // "ph" for φ
    /// ```
    fn to_ascii(&self) -> String {
        format!("{}", self) // Default: use Display
    }

    /// Get UTF-8 representation of this metavariable.
    ///
    /// This provides a Unicode rendering with mathematical symbols
    /// (e.g., φ, ψ, χ for Boolean variables; x, y, z for Setvars).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations should override to provide appropriate
    /// Unicode symbols.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Metavariable, MetaByte, SimpleType};
    ///
    /// let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
    /// let utf8 = var.to_utf8();
    /// assert_eq!(utf8, "P"); // MetaByte uses ASCII
    /// ```
    fn to_utf8(&self) -> String {
        format!("{}", self) // Default: use Display
    }
}
