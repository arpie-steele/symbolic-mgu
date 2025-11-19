//! Introduce the `TypeCore` and `Type` traits.

use crate::MguError;
use std::fmt::{Debug, Display};
use std::hash::Hash;

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
///
/// The `Ord` bound is required to support statement canonicalization,
/// which produces a unique minimal representation by ordering variables
/// lexicographically.
pub trait Type: Clone + Eq + TypeCore + Hash + PartialOrd + Ord
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SimpleType;

    /// Verify that `TypeCore` IS dyn-safe (can be used as a trait object).
    ///
    /// `TypeCore` is intentionally dyn-safe to support error messages and
    /// other scenarios where type information needs to be type-erased.
    /// It omits `Clone`, `Eq`, `Hash`, and `Ord` to maintain dyn-safety.
    #[test]
    fn typecore_is_dyn_safe() {
        let simple_type = SimpleType::Boolean;
        let type_core_ref: &dyn TypeCore = &simple_type;
        assert!(type_core_ref.is_boolean());

        // Can also box it
        let boxed: Box<dyn TypeCore> = Box::new(SimpleType::Setvar);
        assert!(boxed.is_setvar());
    }

    /// Verify that `Type` trait is NOT dyn-safe due to `Clone`, `Eq`, `Hash`, `Ord`.
    ///
    /// `Type` intentionally requires these traits for use in collections and
    /// canonicalization, making it incompatible with trait objects.
    /// The dyn-safe `TypeCore` trait is used for type-erased scenarios.
    #[test]
    fn type_is_not_dyn_safe() {
        // This test documents that Type is NOT dyn-safe by design.
        // The following line would NOT compile (commented out to prevent error):
        //
        // let _: &dyn Type = todo!();
        //
        // Error: Type is not dyn-safe because it requires Clone, Eq, Hash, PartialOrd, Ord
        // which use Self as a type parameter.
        //
        // This is intentional - Type is used as a concrete type in generics like
        // Statement<Ty, V, N, T>, while TypeCore is used for trait objects.
    }

    /// Verify that `to_boxed()` correctly bridges from `Type` to `Box<dyn TypeCore>`.
    #[test]
    fn to_boxed_works() {
        let simple_type = SimpleType::Class;
        let boxed = simple_type.to_boxed();
        assert!(boxed.is_class());
    }
}
