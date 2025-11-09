//! Distinctness graph with Metavariables as vertices.

pub(crate) mod pair;
pub(crate) mod simple_graph;

use crate::{Metavariable, MguError, SimpleGraph};
use std::collections::HashMap;

/// An undirected graph.
#[derive(Debug, PartialEq, Eq, Default)]
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

impl<V: Metavariable> DistinctnessGraph<V> {
    /// Create a new empty distinctness graph.
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
    fn decode_vertex(&self, index: &usize) -> Option<V> {
        self.vars.get(*index).cloned()
    }
}
