//! Very Generic Simple Term implementation.

use crate::{
    Metavariable, MetavariableFactory, MguError, Node, NodeFactory, Term, TermFactory, Type,
};
use std::collections::HashSet;
use std::fmt::Display;

/// A simple implementation of [`Term`] based straightforwardly on supplied [`Metavariable`] and [`Node`] implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(
        bound = "V: serde::Serialize + serde::de::DeserializeOwned, N: serde::Serialize + serde::de::DeserializeOwned"
    )
)]
pub enum EnumTerm<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    /// Variant of a bare [`Metavariable`] leaf.
    Leaf(V),
    /// Variant with a [`Node`] root and some number (possibly zero) children.
    NodeOrLeaf(N, Vec<Self>),
}

impl<T, V, N> EnumTerm<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
}

impl<T, V, N> Display for EnumTerm<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Leaf(v) => {
                write!(f, "{}", v)?;
            }
            Self::NodeOrLeaf(n, c) => {
                write!(f, "[{}", n)?;
                for child in c.iter() {
                    write!(f, ", {}", child)?;
                }
                write!(f, "]")?;
            }
        }
        Ok(())
    }
}

impl<Ty, V, N> Term<Ty, V, N> for EnumTerm<Ty, V, N>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
{
    type Type = Ty;

    type Metavariable = V;

    type Node = N;

    fn is_valid_sentence(&self) -> Result<bool, crate::MguError> {
        match self {
            Self::Leaf(v) => {
                _ = v.get_type_and_index()?; // Just make sure it is "alive"
                Ok(true)
            }
            Self::NodeOrLeaf(n, children) => {
                Self::check_children(n, children)?;
                for child in children {
                    if !child.is_valid_sentence()? {
                        return Ok(false); // We really wanted a reason WHY it was not valid, but pass along the naked false anyway
                    }
                }
                Ok(true)
            }
        }
    }

    fn get_type(&self) -> Result<Ty, crate::MguError> {
        match self {
            Self::Leaf(v) => v.get_type(),
            Self::NodeOrLeaf(n, _) => n.get_type(),
        }
    }

    fn is_metavariable(&self) -> bool {
        match self {
            Self::Leaf(_) => true,
            Self::NodeOrLeaf(_, _) => false,
        }
    }

    fn get_metavariable(&self) -> Option<V> {
        match self {
            Self::Leaf(var) => Some(var.clone()),
            Self::NodeOrLeaf(_, _) => None,
        }
    }

    fn collect_metavariables(&self, vars: &mut HashSet<V>) -> Result<(), MguError> {
        match self {
            Self::Leaf(var) => {
                vars.insert(var.clone());
                Ok(())
            }
            Self::NodeOrLeaf(_, children) => {
                for child in children {
                    child.collect_metavariables(vars)?;
                }
                Ok(())
            }
        }
    }

    fn get_node(&self) -> Option<N> {
        match self {
            Self::Leaf(_) => None,
            Self::NodeOrLeaf(n, _) => Some(n.clone()),
        }
    }

    fn get_n_children(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::NodeOrLeaf(_, c) => c.len(),
        }
    }

    fn get_child(&self, index: usize) -> Option<&Self> {
        match self {
            Self::Leaf(_) => None,
            Self::NodeOrLeaf(_, c) => {
                let n = c.len();
                if index < n {
                    Some(&c[index])
                } else {
                    None
                }
            }
        }
    }

    fn get_children(&self) -> impl Iterator<Item = &Self> {
        match self {
            Self::Leaf(_) => [].iter(),
            Self::NodeOrLeaf(_, c) => c.iter(),
        }
    }

    fn get_children_as_slice(&self) -> &[Self] {
        match self {
            Self::Leaf(_) => &[],
            Self::NodeOrLeaf(_, c) => c.as_slice(),
        }
    }

    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        match self {
            Self::Leaf(v) => v.format_with(formatter),
            Self::NodeOrLeaf(n, children) => {
                if children.is_empty() {
                    // Nullary operator (e.g., True, False)
                    n.format_with(formatter)
                } else if children.len() == 1 {
                    // Unary operator (e.g., Not)
                    let child = children[0].format_with(formatter);
                    format!("{}({})", n.format_with(formatter), child)
                } else {
                    // Binary or n-ary operator (e.g., And, Or, Implies)
                    let formatted_children: Vec<_> =
                        children.iter().map(|c| c.format_with(formatter)).collect();

                    if formatter.is_infix() {
                        // Infix notation: (a ∧ b) or (a → b)
                        let op = n.format_with(formatter);
                        let inner = formatted_children.join(&format!(" {} ", op));
                        format!("({})", inner)
                    } else {
                        // Prefix notation: [And, a, b]
                        let op = n.format_with(formatter);
                        format!("[{}, {}]", op, formatted_children.join(", "))
                    }
                }
            }
        }
    }
}

/// A simple factory for creating [`EnumTerm`] instances.
///
/// This factory creates terms directly without caching or deduplication.
#[derive(Debug)]
pub struct EnumTermFactory<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    /// Phantom data to hold type parameter T.
    _phantom_t: std::marker::PhantomData<T>,
    /// Phantom data to hold type parameter V.
    _phantom_v: std::marker::PhantomData<V>,
    /// Phantom data to hold type parameter N.
    _phantom_n: std::marker::PhantomData<N>,
}

impl<T, V, N> EnumTermFactory<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    /// Create a new `EnumTermFactory`.
    pub fn new() -> Self {
        Self {
            _phantom_t: std::marker::PhantomData,
            _phantom_v: std::marker::PhantomData,
            _phantom_n: std::marker::PhantomData,
        }
    }
}

impl<T, V, N> Default for EnumTermFactory<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, V, N> TermFactory<EnumTerm<T, V, N>, T, V, N> for EnumTermFactory<T, V, N>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    type TermType = T;
    type Term = EnumTerm<T, V, N>;
    type TermNode = N;
    type TermMetavariable = V;

    fn from_factories<VF, NF>(_vars: VF, _nodes: NF) -> Self
    where
        VF: MetavariableFactory<Metavariable = V>,
        NF: NodeFactory<Node = N>,
    {
        Self::new()
    }

    fn create_leaf(&self, var: Self::TermMetavariable) -> Result<Self::Term, MguError> {
        Ok(EnumTerm::Leaf(var))
    }

    fn create_node(
        &self,
        node: Self::TermNode,
        children: Vec<Self::Term>,
    ) -> Result<Self::Term, MguError> {
        // Validate arity
        let expected_arity = node.get_arity()?;
        if children.len() != expected_arity {
            return Err(MguError::SlotsMismatch(expected_arity, children.len()));
        }
        Ok(EnumTerm::NodeOrLeaf(node, children))
    }
}
