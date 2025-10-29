//! Very Generic Simple Term implementation.

use crate::{Metavariable, Node, Term, Type};
use std::fmt::Display;

/// A simple implementation of [`Term`] based straightforwardly on supplied [`Metavariable`] and [`Node`] implementations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
}
