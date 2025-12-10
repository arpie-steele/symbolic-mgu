//! Simple graph for undirected edges.

use crate::{MguError, Pair};
use std::cmp::Ordering;
use std::collections::HashSet;
use std::hash::Hash;

/// Shorthand notation for a complete graph with ½(n²−n) edges for the n distinct vertices.
pub type Clique<U> = Vec<U>;

/// A presentation of the cliques of a simple graph.
pub type Decomposition<U> = Vec<Vec<U>>;

/// Check the essential constraint on Cliques.
///
/// # Errors
///
/// It is an error if the elements aren't in strictly ascending order to guarantee uniqueness.
///
/// It is an error if there are less than two elements.
pub fn check_clique<U: PartialOrd>(source: impl IntoIterator<Item = U>) -> Result<(), MguError> {
    let mut iter = source.into_iter();
    if let Some(first) = iter.next() {
        if let Some(second) = iter.next() {
            if first < second {
                let mut previous = second;
                for value in iter {
                    if previous.partial_cmp(&value) != Some(Ordering::Less) {
                        return Err(MguError::CliqueOrderingError);
                    }
                    previous = value;
                }
                // OK, fall through
            } else {
                return Err(MguError::CliqueOrderingError);
            }
        } else {
            return Err(MguError::CliqueMinimumSizeError);
        }
    } else {
        return Err(MguError::CliqueMinimumSizeError);
    }
    Ok(())
}

/// Check the essential constraint on a Decomposition.
///
/// # Errors
///
/// It is an error if the elements in any Clique aren't in strictly ascending order to guarantee uniqueness.
///
/// It is an error if there are less than two elements in any Clique.
pub fn check_decomposition<U: PartialOrd>(
    source: impl IntoIterator<Item = impl IntoIterator<Item = U>>,
) -> Result<(), MguError> {
    if source.into_iter().any(|x| check_clique(x).is_err()) {
        Err(MguError::DecompositionValidationError)
    } else {
        Ok(())
    }
}

/// A set of [`Pair`] elements is a simple graph.
#[derive(Debug, PartialEq, Eq, Default, Clone)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(bound = "U: serde::Serialize + serde::de::DeserializeOwned + Eq + Hash")
)]
pub struct SimpleGraph<U: Eq + Hash>(HashSet<Pair<U>>);

impl<U: Eq + Hash> SimpleGraph<U> {
    /// Creates an empty `SimpleGraph`.
    #[must_use]
    pub fn new() -> Self {
        Self(HashSet::new())
    }

    /// Returns the number of edges in the graph.
    #[must_use]
    pub fn edges_len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the graph contains no edges.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<U: Eq + Hash> SimpleGraph<U> {
    /// An iterator visiting all edges in arbitrary order.
    /// The iterator element type is `&Pair<U>`.
    pub fn edges_iter(&self) -> impl Iterator<Item = &Pair<U>> {
        self.0.iter()
    }
}

impl<U: std::fmt::Debug + PartialOrd + Eq + Hash> SimpleGraph<U> {
    /// Add an edge (pair) to the graph.
    ///
    /// Returns `Ok(true)` if the edge was newly inserted.
    /// Returns `Ok(false)` if the edge already existed.
    ///
    /// # Errors
    ///
    /// Returns an error if the pair is invalid (elements equal or not comparable).
    pub fn add_pair(&mut self, a: U, b: U) -> Result<bool, MguError> {
        let pair = Pair::new(a, b)?;
        Ok(self.0.insert(pair))
    }
}
