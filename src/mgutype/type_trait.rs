//! Introduce the `TypeCore` and `Type` traits.

use std::fmt::{Debug, Display};

use crate::MguError;

/// Dyn-safe prototype Trait for type systems in formal logic
pub trait TypeCore: Debug + Display {
    /// Is this the Boolean type?
    fn is_boolean(&self) -> bool;

    /// Is this a Setvar type (or sub-type thereof)?
    fn is_setvar(&self) -> bool;

    /// Is this a Class type (or sub-type thereof)?
    fn is_class(&self) -> bool;
}

/// Trait for type systems in formal logic
///
/// Different implementations can have different sub-typing rules and type hierarchies.
/// The library provides a default implementation (Boolean, Setvar, Class) suitable for
/// Metamath and condensed detachment, but other systems can implement custom types.
pub trait Type: Clone + Eq + TypeCore
where
    Self: 'static,
{
    /// Can this type be substituted where `other` is expected?
    ///
    /// Implements sub-typing relationship (e.g., Setvar <: Class in Metamath)
    fn is_subtype_of(&self, other: &Self) -> bool;

    /// Return an object which behaves like the expected Boolean type.
    ///
    /// # Errors
    /// - Not every implementation will support the Boolean type.
    fn try_boolean() -> Result<Self, MguError>;

    /// Return an object which behaves like the expected Setvar type.
    ///
    /// # Errors
    /// - Not every implementation will support the Setvar type.
    fn try_setvar() -> Result<Self, MguError>;

    /// Return an object which behaves like the expected Class type.
    ///
    /// # Errors
    /// - Not every implementation will support the Class type.
    fn try_class() -> Result<Self, MguError>;

    /// Box what is effectively a clone of this object.
    fn to_boxed(&self) -> Box<dyn TypeCore> {
        let obj = self.clone();
        Box::new(obj)
    }
}
