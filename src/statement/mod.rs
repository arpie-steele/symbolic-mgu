//! Define the Statement type.

use crate::{DistinctnessGraph, Metavariable, Term};

/// The primary object representing an axiom, inference rule, or statement of a theorem.
#[derive(Debug, Default, Clone)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(
        bound = "T: serde::Serialize + serde::de::DeserializeOwned, V: serde::Serialize + serde::de::DeserializeOwned"
    )
)]
pub struct Statement<T, V>
where
    T: Term,
    V: Metavariable,
{
    /// The assertion is a sentence which holds true when the hypotheses are met.
    pub(crate) assertion: T,
    /// The optional hypotheses control when the assertion is known to be true.
    pub(crate) hypotheses: Vec<T>,
    /// The distinctness graph controls what variable substitutions are illegal, typically because they threaten self-reference in impermissible ways.
    pub(crate) distinctness_graph: DistinctnessGraph<V>,
}
