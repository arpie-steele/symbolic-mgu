//! Distinctness graphs for tracking variable separation constraints.
//!
//! A distinctness graph records pairs of metavariables that must remain "distinct"—
//! meaning they cannot be substituted with terms that share any common metavariables.
//! This prevents certain invalid substitutions that would conflate logically separate
//! entities.
//!
//! # Semantic Meaning
//!
//! An edge between metavariables `x` and `y` in a distinctness graph means:
//! - `x` and `y` must not be substituted with the same term
//! - More generally, the terms substituted for `x` and `y` must not share any
//!   metavariables in common
//!
//! This is essential for preventing variable capture and maintaining the logical
//! validity of substitutions in quantified formulas or other binding constructs.
//!
//! # Propagation Under Substitution
//!
//! When a substitution is applied to a statement with distinctness constraints:
//!
//! 1. For each edge `(x, y)` in the original graph:
//!    - Let `T_x` be the term substituted for `x` (or `x` itself if unsubstituted)
//!    - Let `T_y` be the term substituted for `y` (or `y` itself if unsubstituted)
//!    - **Validation**: If `T_x` and `T_y` share any metavariables, the substitution
//!      is invalid (distinctness violation)
//!    - **Propagation**: Add edges between every metavariable in `T_x` and every
//!      metavariable in `T_y`
//!
//! 2. When combining statements (e.g., APPLY operation), distinctness graphs are
//!    merged by taking the union of all edges.
//!
//! # Usage
//!
//! Distinctness constraints arise from:
//! - Logical systems with binding constructs (quantifiers, lambda abstractions)
//! - Metamath `$d` statements (see the Metamath book or [`crate::metamath`] module)
//! - Any context where variable separation must be enforced
//!
//! # Example
//!
//! ```
//! use symbolic_mgu::{DistinctnessGraph, MetaByte, SimpleType};
//!
//! let mut graph = DistinctnessGraph::<MetaByte>::new();
//!
//! // Declare that Boolean variables P and Q must be distinct
//! let p = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap(); // P
//! let q = MetaByte::try_from_type_and_index(SimpleType::Boolean, 1).unwrap(); // Q
//! graph.add_edge(&p, &q).unwrap();
//!
//! // Check the constraint exists
//! assert!(graph.has_edge(&p, &q));
//! assert!(graph.has_edge(&q, &p)); // Symmetric
//! ```

pub(crate) mod pair;
pub(crate) mod simple_graph;

use crate::{Metavariable, MguError, SimpleGraph};
use std::collections::HashMap;

/// An undirected graph.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(bound = "V: serde::Serialize + serde::de::DeserializeOwned")
)]
pub struct DistinctnessGraph<V: Metavariable> {
    /// Mapping between [`Metavariable`] and ID.
    vertices: HashMap<V, usize>,
    /// Reverse mapping
    vars: Vec<V>,
    /// Pairs of [`usize`] where the first is smaller than the second.
    edges: SimpleGraph<usize>,
}

impl<V: Metavariable> Clone for DistinctnessGraph<V> {
    fn clone(&self) -> Self {
        Self {
            vertices: self.vertices.clone(),
            vars: self.vars.clone(),
            edges: self.edges.clone(),
        }
    }
}

impl<V: Metavariable> Default for DistinctnessGraph<V> {
    /// Create a new empty distinctness graph.
    ///
    /// This implementation does not require `V: Default` because it creates
    /// an empty graph with no vertices.
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Metavariable> DistinctnessGraph<V> {
    /// Create a new empty distinctness graph.
    #[must_use]
    pub fn new() -> Self {
        Self {
            vertices: HashMap::new(),
            vars: Vec::new(),
            edges: SimpleGraph::new(),
        }
    }

    /// Get an iterator over all edges as (V, V) pairs.
    pub fn edges_iter(&self) -> impl Iterator<Item = (V, V)> + '_ {
        self.edges.edges_iter().filter_map(move |pair| {
            let v1 = self.decode_vertex(&pair[0])?;
            let v2 = self.decode_vertex(&pair[1])?;
            Some((v1, v2))
        })
    }

    /// Check if two metavariables have a distinctness edge.
    #[must_use]
    pub fn has_edge(&self, vertex1: &V, vertex2: &V) -> bool {
        let idx1 = self.vertices.get(vertex1);
        let idx2 = self.vertices.get(vertex2);

        if let (Some(&id1), Some(&id2)) = (idx1, idx2) {
            self.edges.has_pair(id1, id2)
        } else {
            false
        }
    }

    /// Add an edge between two metavariables.
    ///
    /// # Errors
    ///
    /// Returns an error if the pair is invalid.
    pub fn add_edge(&mut self, vertex1: &V, vertex2: &V) -> Result<bool, MguError> {
        let idx1 = self.encode_vertex(vertex1);
        let idx2 = self.encode_vertex(vertex2);
        self.edges.add_pair(idx1, idx2)
    }

    /// Lookup vertex ID for a Metavariable, creating a new ID if needed.
    fn encode_vertex(&mut self, vertex: &V) -> usize {
        if let Some(&idx) = self.vertices.get(vertex) {
            idx
        } else {
            let idx = self.vars.len();
            self.vertices.insert(vertex.clone(), idx);
            self.vars.push(vertex.clone());
            idx
        }
    }

    /// Decode a vertex index back to a Metavariable.
    #[must_use]
    fn decode_vertex(&self, index: &usize) -> Option<V> {
        self.vars.get(*index).cloned()
    }
}
