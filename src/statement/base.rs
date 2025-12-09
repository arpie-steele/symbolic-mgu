//! Core Statement struct and basic operations.
//!
//! This module defines the [`Statement`] type, representing axioms, inference rules,
//! and theorems in a logical system.

use crate::{DistinctnessGraph, Metavariable, MguError, Node, Term, Type};
use std::collections::HashSet;
use std::marker::PhantomData;

/// The primary object representing an axiom, inference rule, or
/// statement of a theorem.
#[derive(Debug, Clone)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(
        bound = "T: serde::Serialize + serde::de::DeserializeOwned, V: serde::Serialize + serde::de::DeserializeOwned"
    )
)]
pub struct Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// This entry is literally not used.
    ///
    /// It functions to remind Rust that this object is tied to a certain Type.
    pub(crate) _not_used: PhantomData<(Ty, N)>,

    /// The assertion is a sentence which holds true when the
    /// hypotheses are met.
    pub(crate) assertion: T,

    /// The optional hypotheses control when the assertion is known
    /// to be true.
    pub(crate) hypotheses: Vec<T>,

    /// The distinctness graph controls what variable substitutions
    /// are illegal, typically because they threaten self-reference
    /// in impermissible ways.
    pub(crate) distinctness_graph: DistinctnessGraph<V>,
}

impl<Ty, V, N, T> Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// Create a new Statement from components.
    ///
    /// # Errors
    ///
    /// Returns an error if the assertion or any hypothesis is not
    /// a valid sentence (where the type is Boolean).
    pub fn new(
        assertion: T,
        hypotheses: Vec<T>,
        distinctness_graph: DistinctnessGraph<V>,
    ) -> Result<Self, MguError> {
        // Validate that assertion is structurally well-formed
        if !assertion.is_valid_sentence()? {
            return Err(MguError::from_found_and_expected_types(
                true,
                &(assertion.get_type()?),
                &(Ty::try_boolean()?),
            ));
        }

        // Validate that assertion has Boolean type (is a sentence)
        let assertion_type = assertion.get_type()?;
        let boolean_type = Ty::try_boolean()?;
        if !assertion_type.is_subtype_of(&boolean_type) {
            return Err(MguError::from_found_and_expected_types(
                true,
                &assertion_type,
                &boolean_type,
            ));
        }

        // Validate that all hypotheses are structurally well-formed and have Boolean type
        for (i, hyp) in hypotheses.iter().enumerate() {
            if !hyp.is_valid_sentence()? {
                return Err(MguError::UnificationFailure(format!(
                    "Hypothesis {i} is not structurally valid (type {:?})",
                    hyp.get_type()
                )));
            }

            // Check that hypothesis has Boolean type
            let hyp_type = hyp.get_type()?;
            if !hyp_type.is_subtype_of(&boolean_type) {
                return Err(MguError::UnificationFailure(format!(
                    "Hypothesis {i} is not a Boolean sentence (type {:?})",
                    hyp_type
                )));
            }
        }

        Ok(Self {
            _not_used: PhantomData,
            assertion,
            hypotheses,
            distinctness_graph,
        })
    }

    /// Create a simple axiom (Statement with no hypotheses and
    /// empty distinctness graph).
    ///
    /// A simple axiom is a statement with:
    /// - An assertion (the axiom itself)
    /// - No hypotheses (empty list)
    /// - No distinctness constraints (empty graph)
    ///
    /// # Errors
    ///
    /// Returns an error if the assertion is not a valid sentence.
    pub fn simple_axiom(assertion: T) -> Result<Self, MguError> {
        Self::new(assertion, Vec::new(), DistinctnessGraph::default())
    }

    /// Access the Assertion Sentence.
    #[must_use]
    pub fn get_assertion(&self) -> &T {
        &self.assertion
    }

    /// Access the Hypotheses Sentences.
    #[must_use]
    pub fn get_hypotheses(&self) -> &Vec<T> {
        &self.hypotheses
    }

    /// Access the Hypotheses Sentences.
    #[must_use]
    pub fn get_n_hypotheses(&self) -> usize {
        self.hypotheses.len()
    }

    /// Access the Hypotheses Sentences.
    #[must_use]
    pub fn get_hypothesis(&self, index: usize) -> Option<&T> {
        self.hypotheses.get(index)
    }

    /// Access the `DistinctnessGraph`.
    #[must_use]
    pub fn get_distinctness_graph(&self) -> &DistinctnessGraph<V> {
        &self.distinctness_graph
    }

    /// Collect all metavariables used in this statement.
    ///
    /// Traverses both the assertion and all hypotheses to collect
    /// every metavariable appearing in the statement.
    ///
    /// # Errors
    ///
    /// Returns an error if any term's structure is malformed or if
    /// metavariable collection fails on any sub-term.
    pub fn collect_metavariables(&self) -> Result<HashSet<V>, MguError> {
        let mut vars = HashSet::new();

        // Collect from assertion
        self.assertion.collect_metavariables(&mut vars)?;

        // Collect from all hypotheses
        for hyp in &self.hypotheses {
            hyp.collect_metavariables(&mut vars)?;
        }

        Ok(vars)
    }
}
