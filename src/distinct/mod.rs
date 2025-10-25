//! Distinctness graph with Metavariables as vertices.

use crate::Metavariable;
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
}

impl<V: Metavariable> Clone for DistinctnessGraph<V> {
    fn clone(&self) -> Self {
        todo!();
    }
}
