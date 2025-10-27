//! Factory pattern for `Node`s.

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
    /// [`Node`]: `crate::Node`
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
    fn count_nodes_by_type(&self, the_type: &Self::NodeType) -> (usize, Option<usize>) {
        (0, None)
    }
}
