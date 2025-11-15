//! Factory for creating [`WideMetavariable`] instances.
//!
//! This module provides [`WideMetavariableFactory`], a stateless factory
//! implementing the [`MetavariableFactory`] trait for [`WideMetavariable`] construction.

use crate::{Metavariable, MetavariableFactory, MguError, SimpleType as Type, WideMetavariable};

/// Stateless factory for creating [`WideMetavariable`] instances.
///
/// This factory provides a simple implementation of the [`MetavariableFactory`]
/// trait, creating [`WideMetavariable`]s on demand without maintaining any state.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::{WideMetavariableFactory, MetavariableFactory, SimpleType, Metavariable};
///
/// let factory = WideMetavariableFactory();
///
/// // Create first Boolean variable
/// let phi = factory.create_by_type_and_index(&SimpleType::Boolean, 0).unwrap();
/// assert_eq!(phi.to_string(), "𝜑");
///
/// // Create with subscript
/// let phi_1 = factory.create_by_type_and_index(&SimpleType::Boolean, 12).unwrap();
/// assert_eq!(phi_1.to_string(), "𝜑₁");
///
/// // Enumerate variables
/// let mut vars = factory.list_metavariables_by_type(&SimpleType::Boolean);
/// assert_eq!(vars.next().unwrap().to_string(), "𝜑");
/// assert_eq!(vars.next().unwrap().to_string(), "𝜓");
/// ```
#[derive(Debug, Clone, Copy, Default)]
pub struct WideMetavariableFactory();

impl WideMetavariableFactory {
    /// Create a new [`WideMetavariableFactory`].
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::WideMetavariableFactory;
    ///
    /// let factory = WideMetavariableFactory::new();
    /// ```
    pub fn new() -> Self {
        WideMetavariableFactory()
    }
}

impl MetavariableFactory for WideMetavariableFactory {
    type Metavariable = WideMetavariable;
    type MetavariableType = Type;
    type MetavariableIterator<'a> = Box<dyn Iterator<Item = WideMetavariable> + 'a>;

    fn create_by_name(&self, name: &str) -> Result<Self::Metavariable, MguError> {
        // WideMetavariable uses UTF-8 display, so name-based creation
        // would require parsing Unicode characters and subscripts.
        // For now, return error - this is primarily an index-based system.
        Err(MguError::from_type_and_var_strings(
            "WideMetavariable",
            name,
        ))
    }

    fn create_by_type_and_index(
        &self,
        the_type: &Self::MetavariableType,
        index: usize,
    ) -> Result<Self::Metavariable, MguError> {
        WideMetavariable::try_from_type_and_index(*the_type, index)
    }

    fn list_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> Self::MetavariableIterator<'_> {
        // Return boxed iterator for unlimited variables
        let typ = *the_type;
        // SAFETY: WideMetavariable::try_from_type_and_index() never fails.
        // It uses modulo arithmetic to map any usize to a valid variable
        // (base character + decorator), so unwrap() will never panic.
        Box::new((0..).map(move |i| WideMetavariable::try_from_type_and_index(typ, i).unwrap()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factory_creates_valid_variables() {
        use crate::metavariable::wide::{WIDE_BOOLEANS, WIDE_CLASSES, WIDE_SETVARS};

        let factory = WideMetavariableFactory::new();

        // Test Boolean creation
        let phi = factory.create_by_type_and_index(&Type::Boolean, 0).unwrap();
        let expected_phi = WIDE_BOOLEANS.chars().next().unwrap().to_string();
        assert_eq!(phi.to_string(), expected_phi);

        let psi = factory.create_by_type_and_index(&Type::Boolean, 1).unwrap();
        let expected_psi = WIDE_BOOLEANS.chars().nth(1).unwrap().to_string();
        assert_eq!(psi.to_string(), expected_psi);

        // Test with subscripts
        let phi_1 = factory
            .create_by_type_and_index(&Type::Boolean, 12)
            .unwrap();
        let expected_phi_1 = WIDE_BOOLEANS.chars().next().unwrap().to_string() + "₁";
        assert_eq!(phi_1.to_string(), expected_phi_1);

        // Test Setvar
        let x = factory.create_by_type_and_index(&Type::Setvar, 0).unwrap();
        let expected_x = WIDE_SETVARS.chars().next().unwrap().to_string();
        assert_eq!(x.to_string(), expected_x);

        // Test Class
        let a = factory.create_by_type_and_index(&Type::Class, 0).unwrap();
        let expected_a = WIDE_CLASSES.chars().next().unwrap().to_string();
        assert_eq!(a.to_string(), expected_a);
    }

    #[test]
    fn factory_list_works() {
        use crate::metavariable::wide::WIDE_BOOLEANS;

        let factory = WideMetavariableFactory::new();

        let vars: Vec<_> = factory
            .list_metavariables_by_type(&Type::Boolean)
            .take(5)
            .collect();
        let expected: Vec<_> = WIDE_BOOLEANS
            .chars()
            .take(5)
            .map(|c| c.to_string())
            .collect();

        assert_eq!(vars[0].to_string(), expected[0]);
        assert_eq!(vars[1].to_string(), expected[1]);
        assert_eq!(vars[2].to_string(), expected[2]);
        assert_eq!(vars[3].to_string(), expected[3]);
        assert_eq!(vars[4].to_string(), expected[4]);
    }

    #[test]
    fn metavariable_max_index_is_large() {
        // Test `max_index` on the Metavariable trait, not the factory
        assert_eq!(
            WideMetavariable::max_index_by_type(Type::Boolean),
            usize::MAX
        );
        assert_eq!(
            WideMetavariable::max_index_by_type(Type::Setvar),
            usize::MAX
        );
        assert_eq!(WideMetavariable::max_index_by_type(Type::Class), usize::MAX);
    }

    #[test]
    fn default_factory_works() {
        use crate::metavariable::wide::WIDE_BOOLEANS;

        let factory = WideMetavariableFactory::default();
        let phi = factory.create_by_type_and_index(&Type::Boolean, 0).unwrap();
        let expected = WIDE_BOOLEANS.chars().next().unwrap().to_string();
        assert_eq!(phi.to_string(), expected);
    }
}
