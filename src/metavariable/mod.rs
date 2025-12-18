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

use crate::formatter::OutputFormatter;
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
    #[must_use]
    fn max_index_by_type(typ: Self::Type) -> usize;

    /// Try to create a metavariable from a type and index.
    ///
    /// # Errors
    /// - Returns an error if the index exceeds the maximum for this type
    /// - Returns an error if the index is incompatible with this type
    fn try_from_type_and_index(my_type: Self::Type, my_index: usize) -> Result<Self, MguError>;

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
    /// use symbolic_mgu::{Metavariable, MetaByte, MetaByteFactory, MetavariableFactory, SimpleType::*, get_formatter};
    ///
    /// let var = MetaByteFactory().list_metavariables_by_type(&Boolean).next().unwrap();
    /// let formatter = get_formatter("utf8");
    /// let output = var.format_with(&*formatter);
    /// assert_eq!(output, "P");
    /// ```
    #[must_use]
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        let _ = formatter; // Suppress unused warning
        format!("{}", self) // Default: use Display
    }

    /// Get ASCII representation of this metavariable.
    ///
    /// This provides a pure ASCII rendering suitable for environments
    /// that don't support Unicode (e.g., plain text terminals).
    ///
    /// # Implementation Notes
    ///
    /// Different implementations may have different conventions:
    /// - `MetaByte`: Returns the ASCII character directly (e.g., "P", "Q", "x")
    /// - `WideMetavariable`: Returns Metamath-style ASCII names (e.g., "ph", "ps", "x")
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Metavariable, MetaByte, MetaByteFactory, MetavariableFactory, SimpleType::*};
    ///
    /// let var = MetaByteFactory().list_metavariables_by_type(&Boolean).next().unwrap();
    /// let ascii = var.to_ascii();
    /// assert_eq!(ascii, "P"); // MetaByte returns literal character
    /// ```
    #[must_use]
    fn to_ascii(&self) -> String {
        format!("{}", self) // Default: use Display
    }

    /// Get UTF-8 representation of this metavariable.
    ///
    /// This may provide Unicode rendering with mathematical symbols depending
    /// on the implementation.
    ///
    /// # Implementation Notes
    ///
    /// Different implementations use different character sets:
    /// - `MetaByte`: ASCII characters only (e.g., "P", "Q", "x")
    /// - `WideMetavariable`: Unicode mathematical symbols (e.g., "𝜑", "𝜓", "𝑥")
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Metavariable, MetaByte, MetaByteFactory, MetavariableFactory, SimpleType::*};
    ///
    /// let var = MetaByteFactory().list_metavariables_by_type(&Boolean).next().unwrap();
    /// let utf8 = var.to_utf8();
    /// assert_eq!(utf8, "P"); // MetaByte uses ASCII only
    /// ```
    #[must_use]
    fn to_utf8(&self) -> String {
        format!("{}", self) // Default: use Display
    }
}

#[cfg(test)]
mod tests {
    /// Verify that Metavariable trait is NOT dyn-safe due to Clone, Eq, Hash, Ord.
    ///
    /// Metavariable intentionally requires these traits for use in collections and
    /// canonicalization, making it incompatible with trait objects.
    /// This is the correct design - Metavariable is used as a concrete type parameter,
    /// not as a trait object.
    #[test]
    fn metavariable_is_not_dyn_safe() {
        // This test documents that Metavariable is NOT dyn-safe by design.
        // The following line would NOT compile (commented out to prevent error):
        //
        // let _: &dyn Metavariable = todo!();
        //
        // Error: Metavariable is not dyn-safe because it requires Clone, Eq, Hash, PartialOrd, Ord
        // which use Self as a type parameter.
        //
        // This is intentional - Metavariable is used as a concrete type in generics like
        // Statement<Ty, V, N, T>, not as a trait object.
    }
}
