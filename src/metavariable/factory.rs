//! Factory pattern for `Metavariable`s.
//!
//! # Factory Pattern Rationale
//!
//! This module implements the **factory pattern** for creating [`Metavariable`] instances.
//! Factories separate **construction strategy** from **behavior**, enabling flexible
//! variable management across different logical systems.
//!
//! ## Why Metavariable Factories?
//!
//! Metavariables represent **logical variables** in formal systems (φ, ψ, x, y, A, B, etc.).
//! Different theorem-proving contexts require different variable management strategies:
//!
//! 1. **Multiple naming conventions**
//!    - Testing: Simple ASCII names ("p", "q", "x", "y")
//!    - Metamath: Numbered variables with type prefixes ("ph", "ps", "x1", "x2")
//!    - Unicode: Greek letters and mathematical symbols ("φ", "ψ", "∀x", "∃y")
//!    - Generated: Fresh variables during proof search ("v0", "v1", "v2", ...)
//!
//! 2. **Type system integration**
//!    - Boolean variables for propositional logic (φ, ψ, χ)
//!    - Set variables for first-order logic (x, y, z)
//!    - Class variables for set theory (A, B, C)
//!    - Domain-specific types (ordinals, real numbers, etc.)
//!
//! 3. **Variable enumeration**
//!    - Fresh variable generation during unification
//!    - Listing all variables of a given type
//!    - Avoiding variable capture during substitution
//!
//! 4. **Different backends**
//!    - Testing: In-memory, simple construction
//!    - Production: Interning, sharing, deduplication
//!    - Database: Persistent variable tables from theorem libraries
//!
//! ## Stateless vs Stateful Factories
//!
//! ### Stateless Factories
//!
//! Stateless factories create variables directly without maintaining state.
//! Suitable for simple variable schemes and testing.
//!
//! ```rust
//! use symbolic_mgu::{MetaByteFactory, MetavariableFactory, SimpleType::*, SimpleTypeFactory};
//!
//! let factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // Create Boolean variables by name (uppercase P-Z)
//! let p = factory.create("P", &Boolean).unwrap();
//! let q = factory.create("Q", &Boolean).unwrap();
//!
//! // Create Setvar/Class by type and index (create_by_name has a bug for these)
//! let x = factory.create_by_type_and_index(&Setvar, 0).unwrap();  // 'x'
//! let y = factory.create_by_type_and_index(&Setvar, 1).unwrap();  // 'y'
//! ```
//!
//! ### Stateful Factories (Conceptual)
//!
//! Stateful factories maintain internal state for variable generation, caching, or database access.
//!
//! ```rust,compile_fail
//! // Hypothetical fresh variable generator
//! struct FreshVariableFactory {
//!     counter: usize,
//!     used_names: HashSet<String>,
//! }
//!
//! impl MetavariableFactory for FreshVariableFactory {
//!     fn create_fresh(&mut self, ty: &SimpleType) -> Result<MetaByte, MguError> {
//!         loop {
//!             let name = format!("v{}", self.counter);
//!             self.counter += 1;
//!
//!             if !self.used_names.contains(&name) {
//!                 self.used_names.insert(name.clone());
//!                 return self.create_by_name(&name);
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! ## Different Backend Examples
//!
//! ### Testing Backend: ASCII Variables
//!
//! Simple factory for unit tests using ASCII variable names:
//!
//! ```rust
//! use symbolic_mgu::{MetaByteFactory, MetavariableFactory, SimpleType::*, SimpleTypeFactory};
//!
//! let factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // Create variables with ASCII names (Boolean uses uppercase P-Z)
//! let phi = factory.create("P", &Boolean).unwrap();
//! let psi = factory.create("Q", &Boolean).unwrap();
//! ```
//!
//! ### Production Backend: Unicode Variables (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical Unicode variable factory
//! let factory = UnicodeMetavariableFactory::new();
//!
//! // Greek letters for Boolean variables
//! let phi = factory.create("φ", &Boolean)?;
//! let psi = factory.create("ψ", &Boolean)?;
//!
//! // Latin letters for set variables
//! let x = factory.create("x", &Setvar)?;
//! let y = factory.create("y", &Setvar)?;
//! ```
//!
//! ### Database Backend: Metamath Integration (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical Metamath variable factory
//! let factory = MetamathVariableFactory::load("set.mm")?;
//!
//! // Variables follow Metamath naming conventions
//! let wph = factory.create("ph", &Boolean)?;  // wff variable
//! let vx = factory.create("x", &Setvar)?;     // setvar variable
//! let cA = factory.create("A", &Class)?;      // class variable
//! ```
//!
//! ## Usage Patterns
//!
//! ### Pattern 1: Creating Variables with Type Constraints
//!
//! ```rust
//! use symbolic_mgu::{MetaByteFactory, MetavariableFactory, SimpleType::*, SimpleTypeFactory};
//!
//! let factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // Type-safe variable creation
//! let phi = factory.create("P", &Boolean).unwrap();
//! let x = factory.create_by_type_and_index(&Setvar, 0).unwrap();  // 'x'
//! let A = factory.create_by_type_and_index(&Class, 0).unwrap();  // 'A'
//! ```
//!
//! ### Pattern 2: Enumerating Variables by Type
//!
//! ```rust
//! use symbolic_mgu::{MetaByteFactory, MetavariableFactory, SimpleType::*, SimpleTypeFactory};
//!
//! let factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // List all Boolean variables
//! let boolean_vars: Vec<_> = factory
//!     .list_metavariables_by_type(&Boolean)
//!     .collect();
//!
//! // List all set variables
//! let setvar_vars: Vec<_> = factory
//!     .list_metavariables_by_type(&Setvar)
//!     .collect();
//! ```
//!
//! ### Pattern 3: Fresh Variable Generation
//!
//! During unification and proof search, we often need to generate fresh variables
//! that don't conflict with existing ones:
//!
//! ```rust
//! use symbolic_mgu::{MetaByteFactory, MetavariableFactory, Metavariable, SimpleType::*, SimpleTypeFactory};
//! use std::collections::HashSet;
//!
//! let factory = MetaByteFactory::new(SimpleTypeFactory);
//!
//! // Collect used variables (Boolean uses uppercase P-Z)
//! let mut used_vars = HashSet::new();
//! used_vars.insert(factory.create("P", &Boolean).unwrap());
//! used_vars.insert(factory.create("Q", &Boolean).unwrap());
//!
//! // Find a fresh variable (simplified example)
//! let fresh = factory.create("R", &Boolean).unwrap();
//! assert!(!used_vars.contains(&fresh));
//! ```
//!
//! ## Design Principles
//!
//! 1. **Factories define HOW** - Variable naming, enumeration, type assignment
//! 2. **Traits define WHAT** - Variable behavior ([`Metavariable::get_type()`], etc.)
//! 3. **Type safety** - Variables carry type constraints (Boolean, Setvar, Class)
//! 4. **Independence** - Separate from [`NodeFactory`] and [`TermFactory`] for clean design
//! 5. **Flexibility** - Support different naming conventions and backends transparently
//!
//! [`Metavariable`]: `crate::Metavariable`
//! [`Metavariable::get_type()`]: `crate::Metavariable::get_type`
//! [`NodeFactory`]: `crate::NodeFactory`
//! [`TermFactory`]: `crate::TermFactory`

use crate::{Metavariable, MguError, Type, TypeFactory};
use std::fmt::Debug;

/// Factory for creating [`Metavariable`] instances
///
/// Implementations may be stateful (caching, interning) or stateless.
/// Supports multiple construction strategies: by name, by code, from database, etc.
///
/// # Type Factory Access
///
/// `MetavariableFactory` provides access to a [`TypeFactory`] via the `type_factory()` method,
/// enabling type construction for production code that already has a metavariable factory.
pub trait MetavariableFactory<TyF>: Debug
where
    TyF: TypeFactory,
    Self::Metavariable: Metavariable<Type = Self::MetavariableType>,
{
    /// Concrete instance of the [`Type`] trait which this factory produces.
    ///
    /// [`Type`]: `crate::Type`
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

    /// Get access to the type factory.
    ///
    /// This allows production code to construct type instances through the metavariable factory:
    ///
    /// ```rust
    /// use symbolic_mgu::{MetaByteFactory, MetavariableFactory, SimpleTypeFactory, TypeFactory};
    ///
    /// let type_factory = SimpleTypeFactory;
    /// let var_factory = MetaByteFactory::new(type_factory);
    ///
    /// // Get Boolean type through the metavariable factory
    /// let bool_type = var_factory.type_factory().try_boolean().unwrap();
    /// let vars = var_factory.list_metavariables_by_type(&bool_type);
    /// ```
    fn type_factory(&self) -> &TyF;

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
    #[must_use]
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
    #[must_use]
    #[allow(unused_variables)]
    fn count_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> (usize, Option<usize>) {
        (0, None)
    }
}
