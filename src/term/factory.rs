//! Factory pattern for `Term`s.

use crate::{Metavariable, MguError, Node, Term, Type};
use std::fmt::Debug;

/// Factory for creating Term instances
///
/// Independent of `NodeFactory` and `MetavariableFactory` for cleaner design and unit testing,
/// even though applications may provide a single object implementing all three.
///
/// Implementations typically cache terms to avoid redundant construction.
pub trait TermFactory: Debug
where
    Self::Term: Term<Type = Self::TermType>,
    Self::TermNode: Node<Type = Self::TermType>,
    Self::TermMetavariable: Metavariable<Type = Self::TermType>,
{
    /// Concrete instance of the Type trait.
    type TermType: Type;

    /// Concrete instance of the Term trait.
    type Term: Term;

    /// Concrete instance of the Node trait.
    type TermNode: Node;

    /// Concrete instance of the Metavariable trait.
    type TermMetavariable: Metavariable;

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
