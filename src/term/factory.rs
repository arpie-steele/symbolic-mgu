//! Factory pattern for `Term`s.

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
