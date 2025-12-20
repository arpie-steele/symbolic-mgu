//! Factory pattern for `Node`s.
//!
//! # Factory Pattern Rationale
//!
//! This module implements the **factory pattern** for creating [`Node`] instances.
//! Factories separate **how objects are constructed** from **what objects can do**,
//! providing a clean architectural boundary between construction strategy and behavior.
//!
//! ## Why Factories?
//!
//! The factory pattern enables:
//!
//! 1. **Multiple construction strategies** - Same trait interface, different implementations
//!    - Stateless: Direct construction (e.g., [`NodeByteFactory`])
//!    - Stateful: Caching, interning, or deduplication
//!    - Database-backed: Load nodes from persistent storage
//!
//! 2. **Separation of concerns** - Construction logic is independent of evaluation logic
//!    - Evaluation code depends only on trait interfaces ([`Node`])
//!    - Factory choice doesn't affect evaluation behavior
//!    - Easy to swap implementations without touching evaluation code
//!
//! 3. **Testability** - Unit tests can use simple in-memory factories
//!    - Production code can use optimized caching factories
//!    - Integration tests can use database factories
//!
//! 4. **Flexibility** - Support different backends transparently
//!    - Testing: Simple direct construction
//!    - Production: Rc/Arc sharing, term deduplication
//!    - Database: Serialized theorem databases (e.g., Metamath)
//!
//! ## Stateless vs Stateful Factories
//!
//! ### Stateless Factories
//!
//! Stateless factories create new objects on each call without maintaining internal state.
//! They're simple, thread-safe by default, and suitable for lightweight nodes.
//!
//! ```rust
//! use symbolic_mgu::{NodeByteFactory, NodeFactory, NodeByte, SimpleType};
//!
//! let factory = NodeByteFactory::<SimpleType>::new();
//!
//! // Each call constructs independently
//! let and1 = factory.create_by_name("And", 2).unwrap();
//! let and2 = factory.create_by_name("And", 2).unwrap();
//!
//! // Both are equal but may be distinct instances (depending on Node's Copy/Clone)
//! assert_eq!(and1, and2);
//! ```
//!
//! ### Stateful Factories (Conceptual)
//!
//! Stateful factories maintain internal state (caches, interning tables, database connections)
//! to optimize construction, enable sharing, or connect to external storage.
//!
//! ```rust,compile_fail
//! // Hypothetical caching factory (not yet implemented)
//! use symbolic_mgu::{NodeFactory, Node, SimpleType};
//! use std::sync::Arc;
//!
//! struct CachingNodeFactory {
//!     cache: HashMap<(String, usize), Arc<ConcreteNode>>,
//! }
//!
//! impl NodeFactory for CachingNodeFactory {
//!     fn create_by_name(&mut self, name: &str, arity: usize) -> Result<Arc<ConcreteNode>, MguError> {
//!         // Check cache first
//!         if let Some(cached) = self.cache.get(&(name.to_string(), arity)) {
//!             return Ok(Arc::clone(cached));
//!         }
//!
//!         // Construct and cache
//!         let node = Arc::new(ConcreteNode::new(name, arity)?);
//!         self.cache.insert((name.to_string(), arity), Arc::clone(&node));
//!         Ok(node)
//!     }
//! }
//! ```
//!
//! ## Different Backend Examples
//!
//! ### Testing Backend: Simple Direct Construction
//!
//! ```rust
//! use symbolic_mgu::{NodeByteFactory, NodeFactory, SimpleType};
//!
//! // Simple factory for unit tests - no caching, minimal overhead
//! let factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//! let implies = factory.create_by_name("Implies", 2).unwrap();
//! let not = factory.create_by_name("Not", 1).unwrap();
//! ```
//!
//! ### Production Backend: Caching (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical production factory with term deduplication
//! let factory = CachingNodeFactory::new();
//!
//! // First call constructs and caches
//! let node1 = factory.create_by_name("Implies", 2);
//!
//! // Second call returns cached Arc (shared ownership, no reconstruction)
//! let node2 = factory.create_by_name("Implies", 2);
//!
//! assert!(Arc::ptr_eq(&node1, &node2)); // Same underlying object
//! ```
//!
//! ### Database Backend: Persistent Storage (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical database-backed factory for Metamath integration
//! let factory = MetamathNodeFactory::connect("theorems.db")?;
//!
//! // Loads node definition from database
//! let node = factory.create_by_name("wi", 2)?; // Metamath's implication
//!
//! // Node contains database metadata (theorem ID, references, etc.)
//! ```
//!
//! ## Usage Patterns
//!
//! ### Pattern 1: Construction Phase (Factory-Dependent)
//!
//! Use factories to construct nodes:
//!
//! ```rust
//! use symbolic_mgu::{NodeByteFactory, NodeFactory, SimpleType, MguError};
//!
//! fn build_logical_nodes<NF>(factory: &NF) -> Result<(), MguError>
//! where
//!     NF: NodeFactory<NodeType = SimpleType>,
//! {
//!     let implies = factory.create_by_name("Implies", 2)?;
//!     let and = factory.create_by_name("And", 2)?;
//!     let not = factory.create_by_name("Not", 1)?;
//!
//!     // Use nodes to construct terms...
//!     Ok(())
//! }
//!
//! // Works with any NodeFactory implementation
//! let simple_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//! build_logical_nodes(&simple_factory).unwrap();
//! ```
//!
//! ### Pattern 2: Evaluation Phase (Factory-Agnostic)
//!
//! Evaluation logic never sees factories:
//!
//! ```rust,compile_fail
//! use symbolic_mgu::{Node, Term, MguError};
//!
//! fn evaluate_term<N, T>(term: &T) -> Result<bool, MguError>
//! where
//!     N: Node,
//!     T: Term<SimpleType, MetaByte, N>,
//! {
//!     // Evaluation depends only on trait interfaces
//!     // Factory choice is completely transparent here
//!     match term.get_node() {
//!         Some(node) => {
//!             // Work with node via Node trait methods
//!             let arity = node.get_arity()?;
//!             // ... evaluation logic ...
//!             Ok(true)
//!         }
//!         None => Ok(false), // Metavariable leaf
//!     }
//! }
//! ```
//!
//! ## Design Principles
//!
//! 1. **Factories define HOW** - Construction strategy (caching, database, etc.)
//! 2. **Traits define WHAT** - Behavior interface ([`Node::get_arity()`], etc.)
//! 3. **Independence** - [`NodeFactory`], [`MetavariableFactory`],
//!    and [`TermFactory`] are separate for cleaner design
//! 4. **Flexibility** - Applications can provide single object implementing all three
//!
//! [`MetavariableFactory`]: `crate::MetavariableFactory`
//! [`Node`]: `crate::Node`
//! [`Node::get_arity()`]: `crate::Node::get_arity`
//! [`NodeByteFactory`]: `crate::NodeByteFactory`
//! [`TermFactory`]: `crate::TermFactory`

use crate::{MguError, Node, Type};
#[cfg(feature = "bigint")]
use num_bigint::BigUint;
use std::fmt::Debug;

/// Factory for creating [`Node`] instances
///
/// Implementations may be stateful (caching, interning) or stateless.
/// Supports multiple construction strategies: by name, by code, from database, etc.
pub trait NodeFactory: Debug
where
    Self::Node: Node<Type = Self::NodeType>,
{
    /// Concrete instance of the [`Type`] trait which this factory produces.
    ///
    /// [`Type`]: `crate::Type`
    type NodeType: Type;

    /// Concrete instance of the [`Node`] trait which this factory produces.
    ///
    /// [`Node`]: `crate::Node`
    type Node: Node;

    /// Concrete instance of an iterator which returns Nodes.
    ///
    type NodeIterator<'a>: Iterator<Item = Self::Node> + 'a
    where
        Self: 'a;

    /// Create a node by human-readable name and arity
    ///
    /// # Arguments
    /// - `name`: Operation name (e.g., "And", "Or", "Implies")
    /// - `arity`: Number of child terms (0 = nullary, 1 = unary, 2 = binary, 3 = ternary, ...)
    ///
    /// # Errors
    /// - Returns error if name is unknown to the factory or arity is
    ///   invalid or unsupported for that operation
    fn create_by_name(&self, name: &str, arity: usize) -> Result<Self::Node, MguError>;

    /// Create a Boolean node by numeric code and arity up to 7.
    ///
    /// # Arguments
    /// - `code`: Operation code where the bit of
    ///   `1 << (if a {1} else {0} | if b {2} else {0} | if c {4} else {0} | ...)`
    ///   is set iff `Operation(a, b, c, ...)` should be true.
    /// - `arity`: Number of child terms, 0..=7 which should be:
    ///    - at least 3 if c is present,
    ///    - at least 2 if b is present,
    ///    - at least 1 if a is present, and
    ///    - at least 0 if there are no variables in the function the `code` stands for.
    ///
    /// # Errors
    /// - Returns error if code is unknown or arity is invalid for the given
    ///   code or if no such instance exists.
    ///
    /// # Warnings
    /// - While Boolean functions on an arbitrary number of inputs exist, we
    ///   support only up to seven because that's the limit of what we could
    ///   implement natively and found three was the limit of what we found
    ///   useful. Concrete user factories may provide alternate functionality
    ///   and lower limits.
    fn create_by_boolean_function_code(
        &self,
        code: u128,
        arity: usize,
    ) -> Result<Self::Node, MguError>;

    /// Create a Boolean node by numeric code and arity.
    ///
    /// # Arguments
    /// - `code`: Operation code where the bit of
    ///   `1 << (if a {1} else {0} | if b {2} else {0} | if c {4} else {0} | ...)`
    ///   is set iff `Operation(a, b, c, ...)` should be true.
    /// - `arity`: Number of child terms, which should be:
    ///    - at least 3 if c is present,
    ///    - at least 2 if b is present,
    ///    - at least 1 if a is present, and
    ///    - at least 0 if there are no variables in the function the `code` stands for.
    ///
    /// # Errors
    /// - Returns error if code is unknown or arity is invalid for the given
    ///   code or if no such instance exists.
    ///
    /// # Warnings
    /// - While Boolean functions on an arbitrary number of inputs exist, we
    ///   found three was the limit of what we found useful.
    #[cfg_attr(nightly, doc(cfg(feature = "bigint")))]
    #[cfg(feature = "bigint")]
    fn create_by_boolean_function_long_code(
        &self,
        code: BigUint,
        arity: usize,
    ) -> Result<Self::Node, MguError>;

    /// Create a node by factory-specific reference to the Node's type and index within the type.
    ///
    /// # Arguments
    /// - `type`: Operation's `Type` conforming to the type of the returned `Node`, if any.
    /// - `index`: A lookup code which may be interpreted by the factory in conjunction with the supplied `type`
    ///
    /// # Errors
    /// - Returns error if the `type` or `index` (or the pair of them) is unsupported, or if the located `Node` is not of type `the_type`
    fn create_by_type_and_index(
        &self,
        the_type: Self::NodeType,
        index: usize,
    ) -> Result<Self::Node, MguError>;

    /// Replicate a node.
    ///
    /// # Errors
    /// - Returns error if the Node cannot be replicated.
    fn replicate_node<N>(&self, node: &N) -> Result<Self::Node, MguError>
    where
        N: Node<Type = Self::NodeType>,
    {
        let (the_type, index) = node.get_type_and_index()?;
        self.create_by_type_and_index(the_type, index)
    }

    /// List all nodes by their Type.
    ///
    /// # Arguments
    /// - `type`: Operation's `Type` conforming to the type of the returned `Node`s.
    ///
    /// # Warning
    /// - This iterator will return unique entries, but not necessarily a number that fits in memory.
    #[must_use]
    fn list_nodes_by_type(&self, the_type: &Self::NodeType) -> Self::NodeIterator<'_>;

    /// Count all nodes by their Type.
    ///
    /// # Arguments
    /// - `type`: Operation's `Type` conforming to the type of the returned `Node`s.
    ///
    /// # Returns
    /// - lower limit on the number of nodes currently returned by `list_nodes_by_type`
    /// - upper limit on the number of nodes currently returned by `list_nodes_by_type` if computable.
    #[allow(unused_variables)]
    #[must_use]
    fn count_nodes_by_type(&self, the_type: &Self::NodeType) -> (usize, Option<usize>) {
        (0, None)
    }
}
