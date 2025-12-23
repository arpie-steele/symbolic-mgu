//! Factory pattern for `Type` construction.
//!
//! This module separates type construction from type capabilities. The [`Type`] trait
//! provides capability checking methods (`is_boolean()`, `is_setvar()`, etc.), while
//! [`TypeFactory`] handles construction of type instances.
//!
//! # Rationale
//!
//! Different type systems require different construction strategies:
//!
//! - **`SimpleType`**: Stateless construction (just return enum variants)
//! - **`DbType`**: Requires database context to construct (needs type code mapping)
//! - **Future types**: May require validation, caching, or other context
//!
//! By separating construction into a factory, we avoid requiring all `Type` implementations
//! to support static construction methods, which was problematic for database-backed types.
//!
//! # Design
//!
//! The factory is passed to other factories ([`TermFactory`], [`MetavariableFactory`]) which
//! expose it via `type_factory()` method. This gives production code access to type
//! construction "for free" through the factories they already have:
//!
//! ```rust
//! use symbolic_mgu::*;
//!
//! let type_factory = SimpleTypeFactory;
//! let term_factory: EnumTermFactory<_, MetaByte, NodeByte, _> = EnumTermFactory::new(SimpleTypeFactory);
//! let var_factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // Get Boolean type through the factory
//! let bool_type = var_factory.type_factory().try_boolean().unwrap();
//! let vars = var_factory.list_metavariables_by_type(&bool_type);
//! ```
//!
//! [`Type`]: `crate::Type``
//! [`TermFactory`]: `crate::TermFactory``
//! [`MetavariableFactory`]: `crate::MetavariableFactory``

use crate::{MguError, SimpleType, Type};
use std::fmt::Debug;

/// Factory for constructing [`Type`] instances.
///
/// This trait provides methods to construct type instances with different semantics
/// (Boolean, Setvar, Class). Different implementations can provide different construction
/// strategies, from simple enum returns to database-backed type lookups.
///
/// # Implementations
///
/// - [`SimpleTypeFactory`]: Stateless factory returning [`SimpleType`] enum variants
/// - `DbTypeFactory`: Database-backed factory (in `metamath` module) returning [`DbType`]
///
/// # Design Pattern
///
/// `TypeFactory` is typically not used directly, but accessed through [`TermFactory`] or
/// [`MetavariableFactory`] via their `type_factory()` method. This provides type
/// construction to code that already has factory access.
///
/// [`Type`]: `crate::Type`
/// [`SimpleType`]: `crate::SimpleType`
/// [`DbType`]: `crate::metamath::DbType`
/// [`TermFactory`]: `crate::TermFactory`
/// [`MetavariableFactory`]: `crate::MetavariableFactory`
pub trait TypeFactory: Debug + Clone {
    /// The concrete [`Type`] implementation this factory produces.
    ///
    /// [`Type`]: `crate::Type`
    type Type: Type;

    /// Construct a Boolean type instance.
    ///
    /// # Errors
    ///
    /// Returns error if the type system does not support Boolean type.
    /// Most implementations (including [`SimpleTypeFactory`]) always succeed.
    fn try_boolean(&self) -> Result<Self::Type, MguError>;

    /// Construct a Setvar type instance.
    ///
    /// # Errors
    ///
    /// Returns error if the type system does not support Setvar type.
    /// Most implementations (including [`SimpleTypeFactory`]) always succeed.
    fn try_setvar(&self) -> Result<Self::Type, MguError>;

    /// Construct a Class type instance.
    ///
    /// # Errors
    ///
    /// Returns error if the type system does not support Class type.
    /// Most implementations (including [`SimpleTypeFactory`]) always succeed.
    fn try_class(&self) -> Result<Self::Type, MguError>;
}

/// Stateless factory for constructing [`SimpleType`] instances.
///
/// This is the default type factory for most use cases. It simply returns
/// the corresponding [`SimpleType`] enum variants with no additional overhead.
///
/// # Examples
///
/// ```rust
/// use symbolic_mgu::{SimpleTypeFactory, TypeFactory, SimpleType};
///
/// let factory = SimpleTypeFactory;
///
/// let bool_type = factory.try_boolean().unwrap();
/// assert_eq!(bool_type, SimpleType::Boolean);
///
/// let setvar_type = factory.try_setvar().unwrap();
/// assert_eq!(setvar_type, SimpleType::Setvar);
///
/// let class_type = factory.try_class().unwrap();
/// assert_eq!(class_type, SimpleType::Class);
/// ```
///
/// [`SimpleType`]: `crate::SimpleType`
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct SimpleTypeFactory;

impl TypeFactory for SimpleTypeFactory {
    type Type = SimpleType;

    fn try_boolean(&self) -> Result<Self::Type, MguError> {
        Ok(Self::Type::Boolean)
    }

    fn try_setvar(&self) -> Result<Self::Type, MguError> {
        Ok(Self::Type::Setvar)
    }

    fn try_class(&self) -> Result<Self::Type, MguError> {
        Ok(Self::Type::Class)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SimpleType;

    #[test]
    fn simple_type_factory_boolean() {
        let factory = SimpleTypeFactory;
        let result = factory.try_boolean();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), SimpleType::Boolean);
    }

    #[test]
    fn simple_type_factory_setvar() {
        let factory = SimpleTypeFactory;
        let result = factory.try_setvar();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), SimpleType::Setvar);
    }

    #[test]
    fn simple_type_factory_class() {
        let factory = SimpleTypeFactory;
        let result = factory.try_class();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), SimpleType::Class);
    }

    #[test]
    fn simple_type_factory_default() {
        let factory = SimpleTypeFactory;
        assert!(factory.try_boolean().is_ok());
    }

    #[test]
    fn simple_type_factory_clone() {
        let factory1 = SimpleTypeFactory;
        let factory2 = factory1;
        assert_eq!(factory1, factory2);
    }
}
