//! Factory pattern for `Metavariable`s.

use crate::{Metavariable, MguError, Type};
use std::fmt::Debug;

/// Factory for creating [`Metavariable`] instances
///
/// Implementations may be stateful (caching, interning) or stateless.
/// Supports multiple construction strategies: by name, by code, from database, etc.
pub trait MetavariableFactory: Debug
where
    Self::Metavariable: Metavariable<Type = Self::MetavariableType>,
{
    /// Concrete instance of the [`Type`] trait which this factory produces.
    ///
    /// [`Metavariable`]: `crate::Metavariable`
    type MetavariableType: Type;

    /// Concrete instance of the [`Metavariable`] trait which this factory produces.
    ///
    /// [`Metavariable`]: `crate::Metavariable`
    type Metavariable: Metavariable;

    /// Concrete instance of an iterator which returns Metavariables.
    ///
    type MetavariableIterator<'a>: Iterator<Item = Self::Metavariable> + 'a
    where
        Self: 'a;

    /// Create a metavariable with name and type constraint
    ///
    /// # Arguments
    /// - `name`: Variable name (e.g., "x", "ph", "A")
    /// - `type_constraint`: Type constraint for this variable
    ///
    /// # Errors
    /// - Returns error if name is invalid or type is not supported
    fn create(
        &self,
        name: &str,
        type_constraint: &Self::MetavariableType,
    ) -> Result<Self::Metavariable, MguError> {
        let item = self.create_by_name(name);
        let item = item?;
        let v = item.get_type()?;
        if v != *type_constraint {
            return Err(MguError::from_found_and_expected_types(
                false,
                &v,
                type_constraint,
            ));
        }
        Ok(item)
    }

    /// Create a Metavariable by human-readable name.
    ///
    /// # Arguments
    /// - `name`: Variable name (e.g., "X", "𝑓", "𝜃₁₅₃₇₂₂₈₆₇₂₈₀₉₁₂₉₃₀₁")
    ///
    /// # Errors
    /// - Returns error if name is unknown to the factory
    fn create_by_name(&self, name: &str) -> Result<Self::Metavariable, MguError>;

    /// Create a Metavariable by factory-specific reference to the `Metavariable`'s type and index within the type.
    ///
    /// # Arguments
    /// - `type`: Operation's `Type` conforming to the type of the returned `Metavariable`, if any.
    /// - `index`: A lookup code which may be interpreted by the factory in conjunction with the supplied `type`
    ///
    /// # Errors
    /// - Returns error if the `type` or `index` (or the pair of them) is unsupported, or if the located `Metavariable` is not of type `the_type`
    fn create_by_type_and_index(
        &self,
        the_type: &Self::MetavariableType,
        index: usize,
    ) -> Result<Self::Metavariable, MguError>;

    /// List all Metavariables by their Type.
    ///
    /// # Arguments
    /// - `type`: Operation's `Type` conforming to the type of the returned `Metavariable`s.
    ///
    /// # Warning
    /// - This iterator will return unique entries, but not necessarily a number that fits in memory.
    fn list_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> Self::MetavariableIterator<'_>;

    /// Count all Metavariables by their Type.
    ///
    /// # Arguments
    /// - `the_type`: Operation's `Type` conforming to the type of the returned `Metavariable`s.
    ///
    /// # Returns
    /// - lower limit on the number of Metavariables currently returned by `list_Metavariables_by_type`
    /// - upper limit on the number of Metavariables currently returned by `list_Metavariables_by_type` if computable.
    #[allow(unused_variables)]
    fn count_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> (usize, Option<usize>) {
        (0, None)
    }
}
