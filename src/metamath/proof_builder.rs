//! Convert unification results to Metamath proof format.
//!
//! This module provides tools for generating Metamath proofs from
//! unification substitutions discovered by symbolic-mgu operations.
//!
//! # Purpose
//!
//! When symbolic-mgu discovers a unification between statements, we want to
//! record this as a Metamath proof. This builder converts:
//!
//! - A `Substitution<DbMetavariable, DbTerm>` from unification
//! - Into a `Proof` (expanded label sequence)
//!
//! # Example Use Case
//!
//! ```text
//! Given:
//!   ax-1: |- ( ph -> ( ps -> ph ) )
//!
//! Apply with substitution:
//!   σ = { ph ↦ (ψ → χ), ps ↦ ψ }
//!
//! Generate proof showing:
//!   |- ( (ψ → χ) -> (ψ -> (ψ → χ)) )
//!
//! Proof: [wph, wps, wch, wi, ax-1]
//!        (floating hyps for ψ, χ, then build implication, then apply ax-1)
//! ```

use crate::metamath::database::MetamathDatabase;
use crate::metamath::label::Label;
use crate::metamath::proof::Proof;
use crate::metamath::symbolic::{DbMetavariable, DbTerm};
use crate::{Metavariable, Substitution, Term};
use std::collections::HashSet;
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during proof building.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ProofBuildError {
    /// Variable in substitution not found in database.
    #[error("Variable '{variable}' not found in database")]
    VariableNotFound {
        /// The variable name
        variable: String,
    },

    /// Cannot represent term in Metamath proof format.
    #[error("Term cannot be represented in Metamath format: {reason}")]
    UnrepresentableTerm {
        /// Reason why term cannot be represented
        reason: String,
    },

    /// Missing required hypothesis.
    #[error("Required hypothesis '{label}' not found")]
    MissingHypothesis {
        /// The hypothesis label
        label: String,
    },

    /// Assertion not found in database.
    #[error("Assertion '{label}' not found in database")]
    AssertionNotFound {
        /// The assertion label
        label: String,
    },
}

/// Builder for constructing Metamath proofs from unification results.
///
/// # Purpose
///
/// When symbolic-mgu discovers a unification between statements, we want to
/// record this as a Metamath proof. This builder converts substitutions
/// into expanded Metamath proof format (label sequences).
///
/// # Example
///
/// ```no_run
/// use symbolic_mgu::metamath::{
///     MetamathDatabase, TypeMapping, ProofBuilder, Label, DbMetavariable, DbTerm,
/// };
/// use symbolic_mgu::Substitution;
/// use std::sync::Arc;
///
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
/// // ... parse database, perform unification ...
///
/// let builder = ProofBuilder::new(Arc::clone(&db));
/// let substitution: Substitution<DbMetavariable, DbTerm> = Substitution::new();
/// // let proof = builder.build_proof(&Label::new("ax-1")?, &substitution)?;
/// # Ok(())
/// # }
/// ```
pub struct ProofBuilder {
    /// Reference to database for variable/hypothesis lookups.
    database: Arc<MetamathDatabase>,
}

impl ProofBuilder {
    /// Create a new proof builder.
    ///
    /// # Arguments
    ///
    /// * `database` - Shared reference to the Metamath database
    ///
    /// # Example
    ///
    /// ```no_run
    /// use symbolic_mgu::metamath::{MetamathDatabase, TypeMapping, ProofBuilder};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let builder = ProofBuilder::new(db);
    /// ```
    pub fn new(database: Arc<MetamathDatabase>) -> Self {
        Self { database }
    }

    /// Build an expanded proof from a substitution.
    ///
    /// This generates a Metamath proof that shows how to instantiate an assertion
    /// (axiom or theorem) with a specific substitution. The proof consists of:
    ///
    /// 1. Floating hypotheses for variables that appear in the substitution
    /// 2. Construction steps for compound terms (if any)
    /// 3. The assertion label itself
    ///
    /// # Arguments
    ///
    /// * `assertion_label` - The axiom/theorem being instantiated
    /// * `substitution` - The substitution from unification
    ///
    /// # Returns
    ///
    /// An expanded `Proof` (label sequence) that instantiates the assertion.
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Assertion not found in database
    /// - Substitution contains variables not in database
    /// - Terms cannot be represented in Metamath format
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use symbolic_mgu::metamath::{
    /// #     MetamathDatabase, TypeMapping, ProofBuilder, Label, DbMetavariable, DbTerm,
    /// # };
    /// # use symbolic_mgu::Substitution;
    /// # use std::sync::Arc;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let builder = ProofBuilder::new(Arc::clone(&db));
    /// let substitution: Substitution<DbMetavariable, DbTerm> = Substitution::new();
    ///
    /// let proof = builder.build_proof(&Label::new("ax-1")?, &substitution)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn build_proof(
        &self,
        assertion_label: &Label,
        _substitution: &Substitution<DbMetavariable, DbTerm>,
    ) -> Result<Proof, ProofBuildError> {
        // Verify assertion exists (either axiom or theorem)
        let _exists = self.database.get_axiom(assertion_label).is_some()
            || self.database.get_theorem(assertion_label).is_some();

        if !_exists {
            return Err(ProofBuildError::AssertionNotFound {
                label: assertion_label.to_string(),
            });
        }

        // Build proof steps
        let mut proof_steps: Vec<Arc<str>> = Vec::new();

        // Phase 3.1: Check if assertion has essential hypotheses
        // Get essential hypothesis count to document in comments
        let n_essential_hyps = if let Some(axiom) = self.database.get_axiom(assertion_label) {
            axiom.core.hypotheses.1.len()
        } else if let Some(theorem) = self.database.get_theorem(assertion_label) {
            theorem.core.hypotheses.1.len()
        } else {
            0
        };

        // For each essential hypothesis, we would need to:
        // 1. Apply substitution to the hypothesis statement
        // 2. Build proof steps for the substituted hypothesis
        // This is deferred to Phase 4 (advanced proof building)
        if n_essential_hyps > 0 {
            // TODO: Phase 4 - Build proofs for essential hypotheses with substitution
        }

        // Phase 3.2: Add the assertion label
        // This is the main step - applying the assertion/axiom/theorem
        proof_steps.push(Arc::from(assertion_label.encoded()));

        // Note: For identity substitution (empty), the proof is just the assertion label
        // For non-trivial substitutions, we would need to add steps to construct
        // the substituted terms before applying the assertion (Phase 3.2 enhancement)

        Ok(Proof::Expanded(proof_steps))
    }

    /// Build an expanded proof from statement application.
    ///
    /// When `Statement::apply()` succeeds with a substitution, this generates
    /// the corresponding Metamath proof.
    ///
    /// # Arguments
    ///
    /// * `major_label` - The statement being applied to
    /// * `minor_label` - The statement being applied
    /// * `substitution` - The resulting substitution
    ///
    /// # Returns
    ///
    /// An expanded proof showing the application.
    ///
    /// # Errors
    ///
    /// Returns error if labels not found or substitution invalid.
    pub fn build_application_proof(
        &self,
        major_label: &Label,
        _minor_label: &Label,
        substitution: &Substitution<DbMetavariable, DbTerm>,
    ) -> Result<Proof, ProofBuildError> {
        // For now, delegate to `build_proof` for the major premise
        // TODO: Phase 4 - Implement full APPLY proof generation
        self.build_proof(major_label, substitution)
    }

    /// Build an expanded proof from condensed detachment.
    ///
    /// When `Statement::condensed_detach()` succeeds, this generates
    /// the corresponding Metamath proof.
    ///
    /// # Arguments
    ///
    /// * `major_label` - The implication being applied
    /// * `minor_label` - The statement matching the antecedent
    /// * `substitution` - The resulting substitution
    ///
    /// # Returns
    ///
    /// An expanded proof showing the condensed detachment.
    ///
    /// # Errors
    ///
    /// Returns error if labels not found or substitution invalid.
    pub fn build_condensed_detachment_proof(
        &self,
        major_label: &Label,
        _minor_label: &Label,
        substitution: &Substitution<DbMetavariable, DbTerm>,
    ) -> Result<Proof, ProofBuildError> {
        // For now, delegate to `build_proof` for the major premise
        // TODO: Phase 4 - Implement full `CONDENSED_DETACH` proof generation
        self.build_proof(major_label, substitution)
    }

    /// Collect all variables that appear in a term.
    ///
    /// This is used to determine which floating hypotheses need to be included
    /// in the proof.
    fn collect_variables(term: &DbTerm) -> HashSet<DbMetavariable> {
        let mut variables = HashSet::new();

        if let Some(var) = term.get_metavariable() {
            // It's a variable - add it
            variables.insert(var.clone());
        } else {
            // It's a node - recursively collect from children
            for child in term.get_children() {
                variables.extend(Self::collect_variables(child));
            }
        }

        variables
    }

    /// Build proof steps to construct a term.
    ///
    /// This generates the sequence of labels needed to build a term from its
    /// constituent variables and nodes.
    ///
    /// # Strategy
    ///
    /// For a variable: Add floating hypothesis label
    /// For a node: Recursively build children, then add node (syntax axiom) label
    ///
    /// # Example
    ///
    /// Term: `(ph -> ps)`
    /// Steps: `["wph", "wps", "wi"]`
    ///        (`FloatingHyp` for `ph`, `FloatingHyp` for `ps`, then implication syntax)
    fn build_term_steps(
        &self,
        term: &DbTerm,
        steps: &mut Vec<Arc<str>>,
    ) -> Result<(), ProofBuildError> {
        if let Some(var) = term.get_metavariable() {
            // It's a variable - add floating hypothesis label
            let var_name = Arc::from(var.to_string());
            let var_type = var
                .get_type()
                .map_err(|_| ProofBuildError::UnrepresentableTerm {
                    reason: format!("Failed to get type for variable {}", var),
                })?;

            let type_code = Arc::from(var_type.to_string());

            if let Some(float_hyp) = self.database.lookup_floating_hyp(&type_code, &var_name) {
                steps.push(Arc::from(float_hyp.label.encoded()));
            } else {
                return Err(ProofBuildError::VariableNotFound {
                    variable: var.to_string(),
                });
            }
        } else if let Some(node) = term.get_node() {
            // It's a node - recursively build children first
            for child in term.get_children() {
                self.build_term_steps(child, steps)?;
            }

            // Then add the node (syntax axiom) label
            steps.push(Arc::from(node.to_string()));
        } else {
            return Err(ProofBuildError::UnrepresentableTerm {
                reason: "Term is neither variable nor node".to_string(),
            });
        }

        Ok(())
    }
}
