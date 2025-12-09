//! Factory pattern for `Term`s.
//!
//! # Factory Pattern Rationale
//!
//! This module implements the **factory pattern** for creating [`Term`] instances.
//! Terms are the core data structures in symbolic logic, representing formulas as trees
//! with metavariable leaves and node heads. Factories enable flexible term construction,
//! caching, and deduplication strategies.
//!
//! ## Why Term Factories?
//!
//! Terms combine [`Metavariable`]s and [`Node`]s into recursive tree structures representing
//! logical formulas. Different use cases require different term construction strategies:
//!
//! 1. **Memory management**
//!    - Testing: Simple direct construction, no sharing
//!    - Production: Term deduplication via interning (save memory)
//!    - Advanced: Rc/Arc sharing for structural sharing
//!    - Database: Lazy loading of terms from persistent storage
//!
//! 2. **Performance optimization**
//!    - Caching: Reuse identical sub-terms instead of reconstructing
//!    - Hash consing: Ensure structural equality = pointer equality
//!    - Memoization: Cache evaluation results alongside terms
//!
//! 3. **Construction validation**
//!    - Type checking during term construction
//!    - Arity validation (node has correct number of children)
//!    - Well-formedness checks (prevent malformed terms)
//!
//! 4. **Backend flexibility**
//!    - Testing: In-memory, simple construction
//!    - Production: Optimized caching and sharing
//!    - Database: Persistent term storage (Metamath, proof libraries)
//!
//! ## Stateless vs Stateful Factories
//!
//! ### Stateless Factories
//!
//! Stateless factories create terms directly without caching or deduplication.
//! Simple, thread-safe, suitable for testing and small-scale use.
//!
//! ```rust
//! use symbolic_mgu::{EnumTermFactory, TermFactory, MetaByteFactory, NodeByteFactory};
//! use symbolic_mgu::{MetavariableFactory, NodeFactory, SimpleType, MetaByte, NodeByte, EnumTerm};
//!
//! let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
//! let metavar_factory = MetaByteFactory();
//! let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//!
//! // Create variable leaf (Boolean uses uppercase P-Z)
//! let p_var = metavar_factory.create("P", &SimpleType::Boolean).unwrap();
//! let p_term = term_factory.create_leaf(p_var).unwrap();
//!
//! // Create compound term: Not(P)
//! let not_node = node_factory.create_by_name("Not", 1).unwrap();
//! let not_p = term_factory.create_node(not_node, vec![p_term]).unwrap();
//! ```
//!
//! ### Stateful Factories (Conceptual)
//!
//! Stateful factories maintain caches for term deduplication and sharing:
//!
//! ```rust,compile_fail
//! // Hypothetical caching term factory
//! use std::collections::HashMap;
//! use std::sync::Arc;
//!
//! struct CachingTermFactory {
//!     // Cache: (node, children) -> shared term
//!     cache: HashMap<(NodeByte, Vec<TermId>), Arc<Term>>,
//!     next_id: usize,
//! }
//!
//! impl TermFactory for CachingTermFactory {
//!     fn create_node(
//!         &mut self,
//!         node: NodeByte,
//!         children: Vec<Arc<Term>>,
//!     ) -> Result<Arc<Term>, MguError> {
//!         // Extract child IDs for cache key
//!         let child_ids: Vec<_> = children.iter().map(|t| t.id).collect();
//!         let key = (node, child_ids);
//!
//!         // Check cache first
//!         if let Some(cached) = self.cache.get(&key) {
//!             return Ok(Arc::clone(cached));
//!         }
//!
//!         // Create new term with unique ID
//!         let term = Arc::new(Term {
//!             id: self.next_id,
//!             node,
//!             children,
//!         });
//!         self.next_id += 1;
//!
//!         // Cache for future reuse
//!         self.cache.insert(key, Arc::clone(&term));
//!         Ok(term)
//!     }
//! }
//! ```
//!
//! ## Different Backend Examples
//!
//! ### Testing Backend: Simple Direct Construction
//!
//! For unit tests, use simple stateless factory with no overhead:
//!
//! ```rust
//! use symbolic_mgu::{EnumTermFactory, TermFactory, MetaByteFactory, NodeByteFactory};
//! use symbolic_mgu::{MetavariableFactory, NodeFactory, SimpleType, MetaByte, NodeByte, EnumTerm};
//!
//! let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
//! let metavar_factory = MetaByteFactory();
//! let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//!
//! // Build: P → Q (Boolean uses uppercase P-Z)
//! let p = metavar_factory.create("P", &SimpleType::Boolean).unwrap();
//! let q = metavar_factory.create("Q", &SimpleType::Boolean).unwrap();
//! let p_term = term_factory.create_leaf(p).unwrap();
//! let q_term = term_factory.create_leaf(q).unwrap();
//!
//! let implies = node_factory.create_by_name("Implies", 2).unwrap();
//! let formula = term_factory.create_node(implies, vec![p_term, q_term]).unwrap();
//! ```
//!
//! ### Production Backend: Term Deduplication (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical production factory with deduplication
//! let mut factory = DeduplicatingTermFactory::new();
//!
//! // Build: (p ∧ p) ∨ (p ∧ p)
//! let p_term1 = factory.create_leaf(p);
//! let p_term2 = factory.create_leaf(p);
//!
//! let and_node = factory.create_by_name("And", 2)?;
//!
//! // First (p ∧ p) - constructs and caches
//! let and1 = factory.create_node(and_node, vec![p_term1.clone(), p_term2.clone()])?;
//!
//! // Second (p ∧ p) - returns cached term (same Arc pointer!)
//! let and2 = factory.create_node(and_node, vec![p_term1, p_term2])?;
//!
//! assert!(Arc::ptr_eq(&and1, &and2)); // Structural sharing
//!
//! // Or node uses shared subterms
//! let or_node = factory.create_by_name("Or", 2)?;
//! let formula = factory.create_node(or_node, vec![and1, and2])?;
//! // Memory savings: single (p ∧ p) stored, referenced twice
//! ```
//!
//! ### Database Backend: Lazy Loading (Conceptual)
//!
//! ```rust,compile_fail
//! // Hypothetical database-backed term factory
//! let factory = DatabaseTermFactory::connect("proofs.db")?;
//!
//! // Load term from database by ID
//! let term_id = 12345;
//! let term = factory.load_term(term_id)?;
//!
//! // Lazy loading: children loaded on demand
//! for child in term.get_children() {
//!     // Child may trigger database query if not already loaded
//!     process(child);
//! }
//! ```
//!
//! ## Usage Patterns
//!
//! ### Pattern 1: Building Terms Bottom-Up
//!
//! Construct terms from leaves to root:
//!
//! ```rust
//! use symbolic_mgu::{EnumTermFactory, TermFactory, MetaByteFactory, NodeByteFactory};
//! use symbolic_mgu::{MetavariableFactory, NodeFactory, SimpleType, MetaByte, NodeByte, EnumTerm};
//!
//! let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
//! let metavar_factory = MetaByteFactory();
//! let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//!
//! // Build: (P ∧ Q) → R (Boolean uses uppercase P-Z)
//! let p = term_factory.create_leaf(
//!     metavar_factory.create("P", &SimpleType::Boolean).unwrap()
//! ).unwrap();
//! let q = term_factory.create_leaf(
//!     metavar_factory.create("Q", &SimpleType::Boolean).unwrap()
//! ).unwrap();
//! let r = term_factory.create_leaf(
//!     metavar_factory.create("R", &SimpleType::Boolean).unwrap()
//! ).unwrap();
//!
//! let and_node = node_factory.create_by_name("And", 2).unwrap();
//! let p_and_q = term_factory.create_node(and_node, vec![p, q]).unwrap();
//!
//! let implies_node = node_factory.create_by_name("Implies", 2).unwrap();
//! let formula = term_factory.create_node(implies_node, vec![p_and_q, r]).unwrap();
//! ```
//!
//! ### Pattern 2: Generic Term Construction
//!
//! Write code generic over any `TermFactory`:
//!
//! ```rust,no_run
//! use symbolic_mgu::{Term, TermFactory, Metavariable, Node, MguError, SimpleType};
//!
//! fn build_implication<TF, T, V, N>(
//!     factory: &TF,
//!     antecedent: T,
//!     consequent: T,
//!     implies_node: N,
//! ) -> Result<T, MguError>
//! where
//!     TF: TermFactory<T, SimpleType, V, N, Term = T, TermNode = N, TermMetavariable = V>,
//!     T: Term<SimpleType, V, N>,
//!     V: Metavariable<Type = SimpleType>,
//!     N: Node<Type = SimpleType>,
//! {
//!     factory.create_node(implies_node, vec![antecedent, consequent])
//! }
//! # fn main() {}
//! ```
//!
//! ### Pattern 3: Validation During Construction
//!
//! Factories can validate well-formedness:
//!
//! ```rust
//! use symbolic_mgu::{EnumTermFactory, TermFactory, MetaByteFactory, NodeByteFactory};
//! use symbolic_mgu::{MetavariableFactory, NodeFactory, SimpleType, MetaByte, NodeByte, EnumTerm};
//!
//! let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
//! let metavar_factory = MetaByteFactory();
//! let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
//!
//! let p = term_factory.create_leaf(
//!     metavar_factory.create("P", &SimpleType::Boolean).unwrap()
//! ).unwrap();
//!
//! // Arity mismatch: Not expects 1 child, but we provide 2
//! let not_node = node_factory.create_by_name("Not", 1).unwrap();
//! let result = term_factory.create_node(not_node, vec![p.clone(), p.clone()]);
//!
//! // Factory validates arity and returns error
//! assert!(result.is_err());
//! ```
//!
//! ## Independence from Other Factories
//!
//! [`TermFactory`] is **independent** from [`NodeFactory`] and
//! [`MetavariableFactory`]:
//!
//! - **Cleaner design**: Each factory has single responsibility
//! - **Easier testing**: Can test term construction separately from node/variable creation
//! - **Flexibility**: Can mix-and-match factory implementations
//!
//! Applications may provide a single object implementing all three traits for convenience:
//!
//! ```rust,compile_fail
//! // Hypothetical unified factory (not yet implemented)
//! struct UnifiedFactory {
//!     nodes: NodeByteFactory,
//!     metavars: MetaByteFactory,
//!     terms: EnumTermFactory,
//! }
//!
//! impl NodeFactory for UnifiedFactory { /* delegate to self.nodes */ }
//! impl MetavariableFactory for UnifiedFactory { /* delegate to self.metavars */ }
//! impl TermFactory for UnifiedFactory { /* delegate to self.terms */ }
//! ```
//!
//! ## Design Principles
//!
//! 1. **Factories define HOW** - Construction strategy (direct, caching, database)
//! 2. **Traits define WHAT** - Term behavior ([`Term::get_type()`], [`Term::get_children()`])
//! 3. **Validation** - Check arity, types, well-formedness during construction
//! 4. **Independence** - Separate from [`NodeFactory`] and [`MetavariableFactory`]
//! 5. **Performance** - Enable caching, deduplication, structural sharing
//! 6. **Flexibility** - Support different backends (testing, production, database)
//!
//! [`Term`]: crate::Term
//! [`Term::get_type()`]: crate::Term::get_type
//! [`Term::get_children()`]: crate::Term::get_children
//! [`Metavariable`]: crate::Metavariable
//! [`Node`]: crate::Node
//! [`NodeFactory`]: crate::NodeFactory
//! [`MetavariableFactory`]: crate::MetavariableFactory

use crate::{Metavariable, MetavariableFactory, MguError, Node, NodeFactory, Term, Type};
use std::fmt::Debug;

/// Factory for creating Term instances
///
/// Independent of `NodeFactory` and `MetavariableFactory` for cleaner design and unit testing,
/// even though applications may provide a single object implementing all three.
///
/// Implementations typically cache terms to avoid redundant construction.
pub trait TermFactory<T, Ty, V, N>: Debug
where
    T: Term<Ty, V, N>,
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
{
    /// Concrete instance of the Type trait.
    type TermType: Type;

    /// Concrete instance of the Term trait.
    type Term: Term<Ty, V, N>;

    /// Concrete instance of the Node trait.
    type TermNode: Node<Type = Ty>;

    /// Concrete instance of the Metavariable trait.
    type TermMetavariable: Metavariable<Type = Ty>;

    /// Create new `TermFactory` from other factories.
    #[must_use]
    fn from_factories<VF, NF>(vars: VF, nodes: NF) -> Self
    where
        VF: MetavariableFactory<Metavariable = V>,
        NF: NodeFactory<Node = N>;

    /// Create a term from a metavariable (leaf node)
    ///
    /// # Errors
    /// - TODO.
    fn create_leaf(&self, var: Self::TermMetavariable) -> Result<Self::Term, MguError>;

    /// Create a term from a node head and children
    ///
    /// # Arguments
    /// - `node`: The operation node
    /// - `children`: Child terms (must match node arity)
    ///
    /// # Errors
    /// - Returns error if children count doesn't match node arity
    /// - May return error if term would violate type constraints
    fn create_node(
        &self,
        node: Self::TermNode,
        children: Vec<Self::Term>,
    ) -> Result<Self::Term, MguError>;
}
