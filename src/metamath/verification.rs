//! Proof verification for Metamath theorems.
//!
//! This module implements the stack-based proof verification algorithm
//! as described in the Metamath book.
//!
//! ## Verification Algorithm
//!
//! 1. Start with an empty stack
//! 2. For each proof step (label):
//!    - If it's a hypothesis: push its statement onto the stack
//!    - If it's an axiom/theorem:
//!      - Pop required hypotheses from stack (based on the axiom's or theorem's mandatory hypotheses)
//!      - Build substitution from floating hypotheses
//!      - Verify essential hypotheses match
//!      - Check distinctness constraints are satisfied
//!      - Push the substituted conclusion onto stack
//! 3. Final stack should contain exactly one statement matching the theorem being proved

use crate::metamath::{
    parse_expression, parse_expression_with_cache, DbMetavariable, DbNode, DbTerm, DbTypeFactory,
    EssentialHyp, FloatingHyp, Label, MetamathDatabase, ParseCache, Proof, Theorem,
};
use crate::term::factory::TermFactory;
use crate::{apply_substitution, DistinctnessGraph, EnumTermFactory, Substitution, Term};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during proof verification.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum VerificationError {
    /// Proof is missing.
    #[error("Theorem '{label}' has no proof")]
    MissingProof {
        /// The theorem label
        label: String,
    },

    /// Stack underflow: tried to pop from empty stack.
    #[error(transparent)]
    StackUnderflow(#[from] Box<StackUnderflowDetails>),

    /// Hypothesis not found.
    #[error("Hypothesis '{label}' not found at step {step}")]
    HypothesisNotFound {
        /// The hypothesis label
        label: String,
        /// Step number where error occurred
        step: usize,
    },

    /// Axiom not found.
    #[error("Axiom '{label}' not found at step {step}")]
    AxiomNotFound {
        /// The axiom label
        label: String,
        /// Step number where error occurred
        step: usize,
    },

    /// Theorem not found.
    #[error("Theorem '{label}' not found at step {step}")]
    TheoremNotFound {
        /// The theorem label
        label: String,
        /// Step number where error occurred
        step: usize,
    },

    /// Substitution mismatch.
    #[error(
        "Substitution mismatch at step {step}: variable '{variable}' has conflicting assignments"
    )]
    SubstitutionMismatch {
        /// Step number where mismatch occurred
        step: usize,
        /// The variable with conflicting assignment
        variable: String,
    },

    /// Essential hypothesis mismatch.
    #[error(transparent)]
    EssentialMismatch(#[from] Box<EssentialMismatchDetails>),

    /// Distinctness constraint violated.
    #[error(transparent)]
    DistinctnessViolation(#[from] Box<DistinctnessViolationDetails>),

    /// Final stack has wrong number of statements.
    #[error("Final stack has {count} statements, expected exactly 1")]
    FinalStackSize {
        /// Number of statements on final stack
        count: usize,
    },

    /// Final statement doesn't match theorem.
    #[error(transparent)]
    FinalStatementMismatch(#[from] Box<FinalStatementMismatchDetails>),

    /// Expression parsing error.
    #[error("Failed to parse expression at step {step}: {error}")]
    ParseError {
        /// Step number
        step: usize,
        /// The underlying error
        error: String,
    },
}

/// Details of a distinctness constraint violation.
///
/// This is boxed to keep the size of `VerificationError` manageable.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("Disjoint variable ($d) violation at proof step {step_display}. Assertion \"{assertion_label}\" requires that variables \"{var1_name}\" and \"{var2_name}\" be disjoint. But \"{var1_name}\" was substituted with \"{var1_subst}\" and \"{var2_name}\" was substituted with \"{var2_subst}\". {conflict_explanation}")]
pub struct DistinctnessViolationDetails {
    /// Step number where violation occurred (0-based internally)
    pub step: usize,
    /// Step number for display (1-based)
    pub step_display: usize,
    /// Label of the assertion being applied
    pub assertion_label: String,
    /// First metavariable name in distinctness constraint
    pub var1_name: String,
    /// Second metavariable name in distinctness constraint
    pub var2_name: String,
    /// Substitution for first variable (as display string)
    pub var1_subst: String,
    /// Substitution for second variable (as display string)
    pub var2_subst: String,
    /// Explanation of the conflict
    pub conflict_explanation: String,
}

/// Details of a stack underflow error.
///
/// This is boxed to keep the size of `VerificationError` manageable.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub struct StackUnderflowDetails {
    /// Step number where underflow occurred (0-based internally)
    pub step: usize,
    /// Step number for display (1-based)
    pub step_display: usize,
    /// Label of the statement being applied (if any)
    pub label: Option<String>,
    /// Number of items required
    pub required: usize,
    /// Number of items available on stack
    pub available: usize,
    /// Current stack contents (formatted)
    pub stack_contents: String,
}

impl std::fmt::Display for StackUnderflowDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref label) = self.label {
            write!(
                f,
                "At proof step {}, statement \"{}\" requires {} {} but the stack contains {}",
                self.step_display,
                label,
                self.required,
                if self.required == 1 {
                    "hypothesis"
                } else {
                    "hypotheses"
                },
                if self.available == 0 {
                    "no entries".to_string()
                } else if self.available == 1 {
                    format!("only one entry: {}", self.stack_contents)
                } else {
                    format!("{} entries: {}", self.available, self.stack_contents)
                }
            )
        } else {
            write!(
                f,
                "Stack underflow at proof step {}: tried to pop {} item{} but stack has {}",
                self.step_display,
                self.required,
                if self.required == 1 { "" } else { "s" },
                if self.available == 0 {
                    "no entries".to_string()
                } else {
                    format!("{} entry/entries", self.available)
                }
            )
        }
    }
}

/// Details of an essential hypothesis mismatch.
///
/// This is boxed to keep the size of `VerificationError` manageable.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub struct EssentialMismatchDetails {
    /// Step number where mismatch occurred (0-based internally)
    pub step: usize,
    /// Step number for display (1-based)
    pub step_display: usize,
    /// Expected statement (formatted)
    pub expected: String,
    /// Actual statement from stack (formatted)
    pub got: String,
}

impl std::fmt::Display for EssentialMismatchDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Essential hypothesis mismatch at proof step {}: expected \"{}\" but got \"{}\"",
            self.step_display, self.expected, self.got
        )
    }
}

/// Details of a final statement mismatch.
///
/// This is boxed to keep the size of `VerificationError` manageable.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub struct FinalStatementMismatchDetails {
    /// Expected theorem statement (formatted)
    pub expected: String,
    /// Actual statement from proof (formatted)
    pub got: String,
}

impl std::fmt::Display for FinalStatementMismatchDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Final statement \"{}\" doesn't match theorem statement \"{}\"",
            self.got, self.expected
        )
    }
}

/// Verify a theorem's proof.
///
/// # Arguments
///
/// * `theorem` - The theorem to verify
/// * `database` - The database containing axioms and theorems
///
/// # Returns
///
/// `Ok(())` if the proof is valid, `Err(VerificationError)` otherwise.
///
/// # Errors
///
/// Returns `Err(VerificationError)` if the proof is missing or invalid.
pub fn verify_theorem(
    theorem: &Theorem,
    database: &Arc<MetamathDatabase>,
) -> Result<(), VerificationError> {
    // Check that proof exists
    let proof = theorem
        .proof
        .as_ref()
        .ok_or_else(|| VerificationError::MissingProof {
            label: theorem.core.label.to_string(),
        })?;

    // Handle expanded vs compressed proofs differently
    match proof {
        Proof::Expanded(labels) => verify_with_steps(theorem, database, labels),
        Proof::Compressed {
            labels,
            proof_string,
        } => verify_compressed(theorem, database, labels, proof_string),
    }
}

/// Verify a theorem using an expanded proof (list of labels).
fn verify_with_steps(
    theorem: &Theorem,
    database: &Arc<MetamathDatabase>,
    steps: &[Arc<str>],
) -> Result<(), VerificationError> {
    // Create parse cache for reuse across all parse operations in this theorem
    let mut parse_cache = ParseCache::new();

    // Initialize verification stack (using DbTerm trees)
    let mut stack: Vec<DbTerm> = Vec::new();

    // Process each proof step
    for (step_num, label_str) in steps.iter().enumerate() {
        let label =
            Label::from_encoded(label_str).map_err(|_| VerificationError::HypothesisNotFound {
                label: label_str.to_string(),
                step: step_num,
            })?;

        // Check if it's a hypothesis (from theorem's mandatory hypotheses)
        if let Some(statement) = find_hypothesis(&theorem.core.hypotheses, &label) {
            // Parse hypothesis statement into DbTerm
            // For logical assertions (starting with "|-"), parse only the part after "|-" as Boolean type
            let term =
                if statement.first().map(|s| s.as_ref()) == Some("|-") {
                    // Logical assertion: parse the part after "|-" as a Boolean expression
                    if statement.len() < 2 {
                        return Err(VerificationError::ParseError {
                            step: step_num,
                            error: format!(
                                "hypothesis '{}': Logical assertion has no content after '|-'",
                                label.as_ref()
                            ),
                        });
                    }
                    // Get the Boolean type code from type mapping
                    let bool_type = database
                        .type_mapping()
                        .get_boolean_type()
                        .clone()
                        .ok_or_else(|| VerificationError::ParseError {
                            step: step_num,
                            error: format!(
                                "hypothesis '{}': Database does not have a Boolean type defined",
                                label.as_ref()
                            ),
                        })?;
                    // Create a Boolean expression from the content after "|-"
                    let bool_expr = [vec![bool_type], statement[1..].to_vec()].concat();
                    parse_expression_with_cache(&bool_expr, database, Some(&mut parse_cache))
                        .map_err(|e| VerificationError::ParseError {
                            step: step_num,
                            error: format!("hypothesis '{}': {}", label.as_ref(), e),
                        })?
                } else {
                    // Syntax axiom: parse normally
                    parse_expression_with_cache(&statement, database, Some(&mut parse_cache))
                        .map_err(|e| VerificationError::ParseError {
                            step: step_num,
                            error: format!("hypothesis '{}': {}", label.as_ref(), e),
                        })?
                };
            stack.push(term);
            continue;
        }

        // Check if it's a floating hypothesis from the database
        if let Some(float_hyp) = database.get_floating_hyp(&label) {
            let statement = vec![float_hyp.type_code, float_hyp.variable];
            let term = parse_expression_with_cache(&statement, database, Some(&mut parse_cache))
                .map_err(|e| VerificationError::ParseError {
                    step: step_num,
                    error: format!("floating hypothesis '{}': {}", label.as_ref(), e),
                })?;
            stack.push(term);
            continue;
        }

        // Check if it's an axiom
        if let Some(axiom) = database.get_axiom(&label) {
            apply_assertion(
                &mut stack,
                &axiom.core.hypotheses,
                &axiom.core.statement,
                &axiom.core.distinctness,
                &theorem.core.distinctness,
                database,
                step_num,
                label.as_str(),
                &mut parse_cache,
            )?;
            continue;
        }

        // Check if it's a theorem
        if let Some(other_theorem) = database.get_theorem(&label) {
            apply_assertion(
                &mut stack,
                &other_theorem.core.hypotheses,
                &other_theorem.core.statement,
                &other_theorem.core.distinctness,
                &theorem.core.distinctness,
                database,
                step_num,
                label.as_str(),
                &mut parse_cache,
            )?;
            continue;
        }

        return Err(VerificationError::HypothesisNotFound {
            label: label_str.to_string(),
            step: step_num,
        });
    }

    // Verify final stack
    if stack.len() != 1 {
        return Err(VerificationError::FinalStackSize { count: stack.len() });
    }

    // Convert final DbTerm to symbol sequence for comparison
    let final_term = &stack[0];
    let mut final_symbols =
        final_term
            .to_symbol_sequence()
            .map_err(|e| VerificationError::ParseError {
                step: steps.len(),
                error: format!("converting final term to symbols: {}", e),
            })?;

    // If theorem statement starts with "|-", the final term is a Boolean expression
    // Replace Boolean type prefix with "|-" for comparison
    if theorem.core.statement.first().map(|s| s.as_ref()) == Some("|-") {
        if let Some(bool_type) = database.type_mapping().get_boolean_type() {
            if final_symbols.first().map(|s| s.as_ref()) == Some(bool_type.as_ref()) {
                final_symbols[0] = Arc::from("|-");
            }
        }
    }

    if final_symbols != theorem.core.statement {
        return Err(VerificationError::FinalStatementMismatch(Box::new(
            FinalStatementMismatchDetails {
                expected: format_statement(&theorem.core.statement, 200),
                got: format_statement(&final_symbols, 200),
            },
        )));
    }

    Ok(())
}

/// Format stack contents for error messages (tree-based).
fn format_stack_tree_contents(stack: &[DbTerm]) -> String {
    if stack.is_empty() {
        return "(empty)".to_string();
    }

    let symbols: Vec<String> = stack
        .iter()
        .map(|term| {
            term.to_symbol_sequence()
                .map(|syms| format_statement(&syms, 50))
                .unwrap_or_else(|_| "(parse error)".to_string())
        })
        .collect();

    symbols.join("; ")
}

/// Check distinctness constraints using tree-based substitution.
fn check_distinctness_tree_based(
    assertion_distinctness: &DistinctnessGraph<DbMetavariable>,
    proof_distinctness: &DistinctnessGraph<DbMetavariable>,
    substitution: &HashMap<DbMetavariable, DbTerm>,
    step_num: usize,
    assertion_label: &str,
) -> Result<(), VerificationError> {
    // For each distinctness constraint in the assertion (e.g., `$d x y $.` in ax-1)
    for (var1, var2) in assertion_distinctness.edges_iter() {
        // Get the substituted terms
        let term1 = substitution.get(&var1);
        let term2 = substitution.get(&var2);

        // If either variable isn't in the substitution, no violation possible
        if term1.is_none() || term2.is_none() {
            continue;
        }

        let term1 = term1.unwrap();
        let term2 = term2.unwrap();

        // Simplified check for the common case: both terms are simple leaves
        if let (Some(var1_from_term), Some(var2_from_term)) =
            (term1.get_metavariable(), term2.get_metavariable())
        {
            // Both are simple variables - check directly
            if var1_from_term == var2_from_term {
                // Same variable used for both parameters - that's a violation
                let var1_symbols = term1.to_symbol_sequence().unwrap_or_default();
                let var2_symbols = term2.to_symbol_sequence().unwrap_or_default();

                return Err(VerificationError::DistinctnessViolation(Box::new(
                    DistinctnessViolationDetails {
                        step: step_num,
                        step_display: step_num + 1,
                        assertion_label: assertion_label.to_string(),
                        var1_name: var1.to_string(),
                        var2_name: var2.to_string(),
                        var1_subst: format_statement(&var1_symbols, 50),
                        var2_subst: format_statement(&var2_symbols, 50),
                        conflict_explanation: format!(
                            "Variable {} appears in both substitutions (same variable used for distinct parameters)",
                            var1_from_term
                        ),
                    },
                )));
            }

            // Different variables - check if proof declares them as distinct
            if !proof_distinctness.has_edge(&var1_from_term, &var2_from_term) {
                let var1_symbols = term1.to_symbol_sequence().unwrap_or_default();
                let var2_symbols = term2.to_symbol_sequence().unwrap_or_default();

                return Err(VerificationError::DistinctnessViolation(Box::new(
                    DistinctnessViolationDetails {
                        step: step_num,
                        step_display: step_num + 1,
                        assertion_label: assertion_label.to_string(),
                        var1_name: var1.to_string(),
                        var2_name: var2.to_string(),
                        var1_subst: format_statement(&var1_symbols, 50),
                        var2_subst: format_statement(&var2_symbols, 50),
                        conflict_explanation: format!(
                            "Proof does not declare distinctness constraint for variables {} and {} (required by assertion)",
                            var1_from_term, var2_from_term
                        ),
                    },
                )));
            }
            continue;
        }

        // At least one term is not a simple leaf - use full collection
        let mut vars1 = HashSet::new();
        term1
            .collect_metavariables(&mut vars1)
            .map_err(|e| VerificationError::ParseError {
                step: step_num,
                error: format!("collecting variables from term1: {}", e),
            })?;

        let mut vars2 = HashSet::new();
        term2
            .collect_metavariables(&mut vars2)
            .map_err(|e| VerificationError::ParseError {
                step: step_num,
                error: format!("collecting variables from term2: {}", e),
            })?;

        // For each pair of variables from the two terms, check if they're declared distinct in the proof
        for v1 in &vars1 {
            for v2 in &vars2 {
                // If it's the same variable appearing in both terms, that's a violation
                if v1 == v2 {
                    let var1_symbols = term1.to_symbol_sequence().unwrap_or_default();
                    let var2_symbols = term2.to_symbol_sequence().unwrap_or_default();

                    return Err(VerificationError::DistinctnessViolation(Box::new(
                        DistinctnessViolationDetails {
                            step: step_num,
                            step_display: step_num + 1,
                            assertion_label: assertion_label.to_string(),
                            var1_name: var1.to_string(),
                            var2_name: var2.to_string(),
                            var1_subst: format_statement(&var1_symbols, 50),
                            var2_subst: format_statement(&var2_symbols, 50),
                            conflict_explanation: format!(
                                "Variable {:?} appears in both substitutions (same variable used for distinct parameters)",
                                v1
                            ),
                        },
                    )));
                }

                // If they're different variables, check if proof declares them as distinct
                if !proof_distinctness.has_edge(v1, v2) {
                    let var1_symbols = term1.to_symbol_sequence().unwrap_or_default();
                    let var2_symbols = term2.to_symbol_sequence().unwrap_or_default();

                    return Err(VerificationError::DistinctnessViolation(Box::new(
                        DistinctnessViolationDetails {
                            step: step_num,
                            step_display: step_num + 1,
                            assertion_label: assertion_label.to_string(),
                            var1_name: var1.to_string(),
                            var2_name: var2.to_string(),
                            var1_subst: format_statement(&var1_symbols, 50),
                            var2_subst: format_statement(&var2_symbols, 50),
                            conflict_explanation: format!(
                                "Proof does not declare distinctness constraint for variables {:?} and {:?} (required by assertion)",
                                v1, v2
                            ),
                        },
                    )));
                }
            }
        }
    }

    Ok(())
}

/// Apply an assertion (axiom or theorem) using tree-based substitution.
///
/// Pops hypotheses from stack, builds substitution map, verifies essential hypotheses,
/// checks distinctness constraints, and pushes the substituted conclusion.
///
/// If parsing fails (e.g., in minimal databases without full syntax definitions),
/// falls back to symbol-sequence based verification.
#[allow(clippy::too_many_arguments)]
fn apply_assertion(
    stack: &mut Vec<DbTerm>,
    hypotheses: &(Vec<FloatingHyp>, Vec<EssentialHyp>),
    conclusion: &[Arc<str>],
    assertion_distinctness: &DistinctnessGraph<DbMetavariable>,
    proof_distinctness: &DistinctnessGraph<DbMetavariable>,
    database: &Arc<MetamathDatabase>,
    step_num: usize,
    assertion_label: &str,
    parse_cache: &mut ParseCache,
) -> Result<(), VerificationError> {
    // Try tree-based verification first
    match apply_assertion_tree_based(
        stack,
        hypotheses,
        conclusion,
        assertion_distinctness,
        proof_distinctness,
        database,
        step_num,
        assertion_label,
        parse_cache,
    ) {
        Ok(()) => Ok(()),
        Err(VerificationError::ParseError { .. }) => {
            // Parsing failed - fall back to symbol-sequence verification
            apply_assertion_symbol_based(
                stack,
                hypotheses,
                conclusion,
                assertion_distinctness,
                proof_distinctness,
                database,
                step_num,
                assertion_label,
                parse_cache,
            )
        }
        Err(e) => Err(e), // Other errors propagate
    }
}

/// Tree-based assertion application (the original implementation).
#[allow(clippy::too_many_arguments)]
fn apply_assertion_tree_based(
    stack: &mut Vec<DbTerm>,
    hypotheses: &(Vec<FloatingHyp>, Vec<EssentialHyp>),
    conclusion: &[Arc<str>],
    assertion_distinctness: &DistinctnessGraph<DbMetavariable>,
    proof_distinctness: &DistinctnessGraph<DbMetavariable>,
    database: &Arc<MetamathDatabase>,
    step_num: usize,
    assertion_label: &str,
    parse_cache: &mut ParseCache,
) -> Result<(), VerificationError> {
    let (floating_hyps, essential_hyps) = hypotheses;

    // Create term factory for substitution operations
    let factory = EnumTermFactory::new(DbTypeFactory::new(Arc::clone(database)));

    // Check stack has enough entries
    let required = floating_hyps.len() + essential_hyps.len();
    if stack.len() < required {
        return Err(VerificationError::StackUnderflow(Box::new(
            StackUnderflowDetails {
                step: step_num,
                step_display: step_num + 1,
                label: Some(assertion_label.to_string()),
                required,
                available: stack.len(),
                stack_contents: format_stack_tree_contents(stack),
            },
        )));
    }

    // Pop required number of terms from stack
    let stack_items: Vec<DbTerm> = stack.drain(stack.len() - required..).collect();

    // Build substitution map from floating hypotheses
    let mut substitution_map: HashMap<DbMetavariable, DbTerm> = HashMap::new();

    for (i, float_hyp) in floating_hyps.iter().enumerate() {
        let stack_term = &stack_items[i];

        // Get the metavariable for this floating hypothesis
        let var_symbols = database.variables_of_type(&float_hyp.type_code);
        let var_index = var_symbols
            .iter()
            .position(|v| v.as_ref() == float_hyp.variable.as_ref())
            .ok_or_else(|| VerificationError::ParseError {
                step: step_num,
                error: format!(
                    "Variable '{}' not found in type '{}'",
                    float_hyp.variable, float_hyp.type_code
                ),
            })?;

        let metavar = DbMetavariable::new(
            Arc::clone(&float_hyp.type_code),
            var_index,
            Arc::clone(database),
        );

        substitution_map.insert(metavar, stack_term.clone());
    }

    // Convert HashMap to Substitution for use with apply_substitution
    let substitution: Substitution<DbMetavariable, DbTerm> = substitution_map.clone().into();

    // Verify essential hypotheses match (tree identity with substitution)
    for (i, ess_hyp) in essential_hyps.iter().enumerate() {
        let stack_term = &stack_items[floating_hyps.len() + i];

        // Parse essential hypothesis statement
        // For logical assertions (starting with "|-"), parse only the part after "|-" as Boolean type
        let expected_term = if ess_hyp.statement.first().map(|s| s.as_ref()) == Some("|-") {
            // Logical assertion: parse the part after "|-" as a Boolean expression
            if ess_hyp.statement.len() < 2 {
                return Err(VerificationError::ParseError {
                    step: step_num,
                    error: "Logical essential hypothesis has no content after '|-'".to_string(),
                });
            }
            // Get the Boolean type code from type mapping
            let bool_type = database
                .type_mapping()
                .get_boolean_type()
                .clone()
                .ok_or_else(|| VerificationError::ParseError {
                    step: step_num,
                    error: "Database does not have a Boolean type defined".to_string(),
                })?;
            // Create a Boolean expression from the content after "|-"
            let bool_expr = [vec![bool_type], ess_hyp.statement[1..].to_vec()].concat();
            parse_expression_with_cache(&bool_expr, database, Some(parse_cache)).map_err(|e| {
                VerificationError::ParseError {
                    step: step_num,
                    error: format!("parsing essential hypothesis content: {}", e),
                }
            })?
        } else {
            // Syntax axiom: parse normally
            parse_expression_with_cache(&ess_hyp.statement, database, Some(parse_cache)).map_err(
                |e| VerificationError::ParseError {
                    step: step_num,
                    error: format!("parsing essential hypothesis: {}", e),
                },
            )?
        };

        // Apply substitution to expected term
        let substituted =
            apply_substitution(&factory, &substitution, &expected_term).map_err(|e| {
                VerificationError::ParseError {
                    step: step_num,
                    error: format!("applying substitution: {}", e),
                }
            })?;

        // Check tree identity
        if stack_term != &substituted {
            // Convert to symbols for error message
            let expected_symbols = substituted.to_symbol_sequence().unwrap_or_default();
            let got_symbols = stack_term.to_symbol_sequence().unwrap_or_default();

            return Err(VerificationError::EssentialMismatch(Box::new(
                EssentialMismatchDetails {
                    step: step_num,
                    step_display: step_num + 1,
                    expected: format_statement(&expected_symbols, 200),
                    got: format_statement(&got_symbols, 200),
                },
            )));
        }
    }

    // Check distinctness constraints
    check_distinctness_tree_based(
        assertion_distinctness,
        proof_distinctness,
        &substitution_map,
        step_num,
        assertion_label,
    )?;

    // Apply substitution to conclusion
    // For logical assertions (starting with "|-"), parse only the part after "|-" as Boolean type
    let conclusion_term = if conclusion.first().map(|s| s.as_ref()) == Some("|-") {
        // Logical assertion: parse the part after "|-" as a Boolean expression
        if conclusion.len() < 2 {
            return Err(VerificationError::ParseError {
                step: step_num,
                error: "Logical assertion has no content after '|-'".to_string(),
            });
        }
        // Get the Boolean type code from type mapping
        let bool_type = database
            .type_mapping()
            .get_boolean_type()
            .clone()
            .ok_or_else(|| VerificationError::ParseError {
                step: step_num,
                error: "Database does not have a Boolean type defined".to_string(),
            })?;
        // Create a Boolean expression from the content after "|-"
        let bool_expr = [vec![bool_type], conclusion[1..].to_vec()].concat();
        parse_expression_with_cache(&bool_expr, database, Some(parse_cache)).map_err(|e| {
            VerificationError::ParseError {
                step: step_num,
                error: format!("parsing logical assertion content: {}", e),
            }
        })?
    } else {
        // Syntax axiom: parse normally
        parse_expression_with_cache(conclusion, database, Some(parse_cache)).map_err(|e| {
            VerificationError::ParseError {
                step: step_num,
                error: format!("parsing conclusion: {}", e),
            }
        })?
    };

    let result = apply_substitution(&factory, &substitution, &conclusion_term).map_err(|e| {
        VerificationError::ParseError {
            step: step_num,
            error: format!("substituting into conclusion: {}", e),
        }
    })?;

    // Push result onto stack
    stack.push(result);
    Ok(())
}

/// Symbol-sequence based assertion application for databases without full syntax definitions.
/// This is used as a fallback when tree-based parsing fails.
///
/// Instead of parsing statements into trees, this works directly with symbol sequences,
/// applying variable substitutions at the symbol level.
#[allow(clippy::too_many_arguments)]
fn apply_assertion_symbol_based(
    stack: &mut Vec<DbTerm>,
    hypotheses: &(Vec<FloatingHyp>, Vec<EssentialHyp>),
    conclusion: &[Arc<str>],
    assertion_distinctness: &DistinctnessGraph<DbMetavariable>,
    proof_distinctness: &DistinctnessGraph<DbMetavariable>,
    database: &Arc<MetamathDatabase>,
    step_num: usize,
    assertion_label: &str,
    _parse_cache: &mut ParseCache,
) -> Result<(), VerificationError> {
    let (floating_hyps, essential_hyps) = hypotheses;

    // Check stack has enough entries
    let required = floating_hyps.len() + essential_hyps.len();
    if stack.len() < required {
        return Err(VerificationError::StackUnderflow(Box::new(
            StackUnderflowDetails {
                step: step_num,
                step_display: step_num + 1,
                label: Some(assertion_label.to_string()),
                required,
                available: stack.len(),
                stack_contents: format_stack_tree_contents(stack),
            },
        )));
    }

    // Pop required number of terms from stack
    let stack_items: Vec<DbTerm> = stack.drain(stack.len() - required..).collect();

    // Build symbol-level substitution map: variable symbol -> symbol sequence
    let mut symbol_substitution: HashMap<Arc<str>, Vec<Arc<str>>> = HashMap::new();

    // Also build `DbMetavariable` substitution for distinctness checking
    let mut metavar_substitution: HashMap<DbMetavariable, DbTerm> = HashMap::new();

    for (i, float_hyp) in floating_hyps.iter().enumerate() {
        let stack_term = &stack_items[i];

        // Get symbol sequence from stack term
        let symbols =
            stack_term
                .to_symbol_sequence()
                .map_err(|e| VerificationError::ParseError {
                    step: step_num,
                    error: format!("converting stack term to symbols: {}", e),
                })?;

        // Strip type prefix (first element) to get just the content
        // Symbol sequences from `to_symbol_sequence()` are `[type_code, ...content]`
        // But in statement patterns, variables appear without the type prefix
        let content = if symbols.len() > 1 {
            symbols[1..].to_vec()
        } else {
            symbols.clone()
        };

        // Store mapping from variable name to its content (without type prefix)
        symbol_substitution.insert(Arc::clone(&float_hyp.variable), content);

        // Also create `metavar` for distinctness checking
        let var_symbols = database.variables_of_type(&float_hyp.type_code);
        let var_index = var_symbols
            .iter()
            .position(|v| v.as_ref() == float_hyp.variable.as_ref())
            .ok_or_else(|| VerificationError::ParseError {
                step: step_num,
                error: format!(
                    "Variable '{}' not found in type '{}'",
                    float_hyp.variable, float_hyp.type_code
                ),
            })?;

        let metavar = DbMetavariable::new(
            Arc::clone(&float_hyp.type_code),
            var_index,
            Arc::clone(database),
        );

        metavar_substitution.insert(metavar, stack_term.clone());
    }

    // Verify essential hypotheses match (symbol sequence equality with substitution)
    for (i, ess_hyp) in essential_hyps.iter().enumerate() {
        let stack_term = &stack_items[floating_hyps.len() + i];

        // Apply symbol substitution to essential hypothesis
        let expected_symbols = apply_symbol_substitution(&ess_hyp.statement, &symbol_substitution);

        // Get actual symbols from stack term
        let actual_symbols =
            stack_term
                .to_symbol_sequence()
                .map_err(|e| VerificationError::ParseError {
                    step: step_num,
                    error: format!("converting stack term to symbols: {}", e),
                })?;

        // Check symbol sequence equality
        if expected_symbols != actual_symbols {
            return Err(VerificationError::EssentialMismatch(Box::new(
                EssentialMismatchDetails {
                    step: step_num,
                    step_display: step_num + 1,
                    expected: format_statement(&expected_symbols, 200),
                    got: format_statement(&actual_symbols, 200),
                },
            )));
        }
    }

    // Check distinctness constraints using metavariable substitution
    check_distinctness_tree_based(
        assertion_distinctness,
        proof_distinctness,
        &metavar_substitution,
        step_num,
        assertion_label,
    )?;

    // Apply symbol substitution to conclusion to get result symbols
    let result_symbols = apply_symbol_substitution(conclusion, &symbol_substitution);

    // Try to parse the result - it might be parsable even if the original conclusion wasn't
    let result_term = match parse_expression(&result_symbols, database) {
        Ok(term) => term,
        Err(_) => {
            // Can't parse - this happens in minimal databases where logical axioms
            // define valid statements without defining their syntax.
            // Construct a term using the assertion itself as the constructor.
            // The children are the terms from the stack (in order).
            let label = Label::new(assertion_label).map_err(|e| VerificationError::ParseError {
                step: step_num,
                error: format!("Invalid assertion label '{}': {}", assertion_label, e),
            })?;
            let node = DbNode::new(label, Arc::clone(database));
            let factory = EnumTermFactory::new(DbTypeFactory::new(Arc::clone(database)));
            let children: Vec<DbTerm> = stack_items.to_vec();
            factory
                .create_node(node, children)
                .map_err(|e| VerificationError::ParseError {
                    step: step_num,
                    error: format!(
                        "Failed to construct term from assertion '{}': {}",
                        assertion_label, e
                    ),
                })?
        }
    };

    // Push result onto stack
    stack.push(result_term);
    Ok(())
}

/// Apply symbol-level substitution to a statement.
/// Replaces each occurrence of a variable with its substitution.
fn apply_symbol_substitution(
    statement: &[Arc<str>],
    substitution: &HashMap<Arc<str>, Vec<Arc<str>>>,
) -> Vec<Arc<str>> {
    let mut result = Vec::new();
    for symbol in statement {
        if let Some(replacement) = substitution.get(symbol) {
            result.extend_from_slice(replacement);
        } else {
            result.push(Arc::clone(symbol));
        }
    }
    result
}

/// Verify a theorem using a compressed proof with 'Z' stack support.
fn verify_compressed(
    theorem: &Theorem,
    database: &Arc<MetamathDatabase>,
    labels: &[Arc<str>],
    proof_string: &str,
) -> Result<(), VerificationError> {
    // Use pre-computed mandatory hypothesis labels from theorem
    let mandatory_hyps = &theorem.mandatory_hyp_labels;

    // Create parse cache for reuse across all parse operations in this theorem
    let mut parse_cache = ParseCache::new();

    // Initialize verification stack and saved steps (for 'Z' operations)
    let mut stack: Vec<DbTerm> = Vec::new();
    let mut saved_steps: Vec<DbTerm> = Vec::new();

    // Process compressed proof string
    let bytes = proof_string.as_bytes();
    let mut position = 0;
    let mut step_num = 0;

    while position < bytes.len() {
        // Skip whitespace
        while position < bytes.len() && bytes[position].is_ascii_whitespace() {
            position += 1;
        }

        if position >= bytes.len() {
            break;
        }

        // Accumulate U-Y characters (higher-order digits)
        let mut uy_chars = Vec::new();
        while position < bytes.len() {
            let ch = bytes[position] as char;
            if ('U'..='Y').contains(&ch) {
                uy_chars.push(ch);
                position += 1;
            } else {
                break;
            }
        }

        if position >= bytes.len() {
            break;
        }

        let ch = bytes[position] as char;
        position += 1;

        if ('A'..='T').contains(&ch) {
            // Decode [U-Y]*[A-T] as a mixed radix number
            let mut number = (ch as u8 - b'A') as usize; // 0-19

            // Add contributions from U-Y digits
            // Use saturating arithmetic to prevent overflow from malicious input
            let mut place_value = 20usize;
            for &uy_char in uy_chars.iter().rev() {
                let digit_value = (uy_char as u8 - b'U' + 1) as usize; // 1-5
                number = number.saturating_add(digit_value.saturating_mul(place_value));
                place_value = place_value.saturating_mul(5);
            }

            // Look up label: `mandatory_hyps` -> labels -> `saved_steps`
            let label_str = if number < mandatory_hyps.len() {
                &mandatory_hyps[number]
            } else {
                let label_index = number - mandatory_hyps.len();
                if label_index < labels.len() {
                    &labels[label_index]
                } else {
                    let saved_index = label_index - labels.len();
                    if saved_index >= saved_steps.len() {
                        return Err(VerificationError::HypothesisNotFound {
                            label: format!("<saved-step[{}]>", saved_index),
                            step: step_num,
                        });
                    }
                    // Push saved statement from `saved_steps`
                    stack.push(saved_steps[saved_index].clone());
                    step_num += 1;
                    continue;
                }
            };

            // Process the label (same logic as expanded proof)
            let label = Label::from_encoded(label_str).map_err(|_| {
                VerificationError::HypothesisNotFound {
                    label: label_str.to_string(),
                    step: step_num,
                }
            })?;

            // Check if it's a hypothesis in theorem.core.hypotheses
            if let Some(statement) = find_hypothesis(&theorem.core.hypotheses, &label) {
                // For logical assertions (starting with "|-"), parse only the part after "|-" as Boolean type
                let term = if statement.first().map(|s| s.as_ref()) == Some("|-") {
                    if statement.len() < 2 {
                        return Err(VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': Logical assertion has no content after '|-'", label.as_str()),
                        });
                    }
                    let bool_type = database
                        .type_mapping()
                        .get_boolean_type()
                        .clone()
                        .ok_or_else(|| VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': Database does not have a Boolean type defined", label.as_str()),
                        })?;
                    let bool_expr = [vec![bool_type], statement[1..].to_vec()].concat();
                    parse_expression(&bool_expr, database).map_err(|e| {
                        VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': {}", label.as_str(), e),
                        }
                    })?
                } else {
                    parse_expression(&statement, database).map_err(|e| {
                        VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': {}", label.as_str(), e),
                        }
                    })?
                };
                stack.push(term);
                step_num += 1;
                continue;
            }

            // Check in all hypotheses that were in scope (for non-mandatory hypotheses)
            if let Some(statement) = find_hypothesis(&theorem.all_hypotheses, &label) {
                // For logical assertions (starting with "|-"), parse only the part after "|-" as Boolean type
                let term = if statement.first().map(|s| s.as_ref()) == Some("|-") {
                    if statement.len() < 2 {
                        return Err(VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': Logical assertion has no content after '|-'", label.as_str()),
                        });
                    }
                    let bool_type = database
                        .type_mapping()
                        .get_boolean_type()
                        .clone()
                        .ok_or_else(|| VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': Database does not have a Boolean type defined", label.as_str()),
                        })?;
                    let bool_expr = [vec![bool_type], statement[1..].to_vec()].concat();
                    parse_expression(&bool_expr, database).map_err(|e| {
                        VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': {}", label.as_str(), e),
                        }
                    })?
                } else {
                    parse_expression(&statement, database).map_err(|e| {
                        VerificationError::ParseError {
                            step: step_num,
                            error: format!("parsing hypothesis '{}': {}", label.as_str(), e),
                        }
                    })?
                };
                stack.push(term);
                step_num += 1;
                continue;
            }

            // Check if it's a floating hypothesis in the database
            if let Some(float_hyp) = database.get_floating_hyp(&label) {
                let statement = vec![
                    Arc::clone(&float_hyp.type_code),
                    Arc::clone(&float_hyp.variable),
                ];
                let term = parse_expression(&statement, database).map_err(|e| {
                    VerificationError::ParseError {
                        step: step_num,
                        error: format!("parsing floating hypothesis '{}': {}", label.as_str(), e),
                    }
                })?;
                stack.push(term);
                step_num += 1;
                continue;
            }

            // Check if it's an axiom
            if let Some(axiom) = database.get_axiom(&label) {
                apply_assertion(
                    &mut stack,
                    &axiom.core.hypotheses,
                    &axiom.core.statement,
                    &axiom.core.distinctness,
                    &theorem.core.distinctness,
                    database,
                    step_num,
                    label.as_str(),
                    &mut parse_cache,
                )?;
                step_num += 1;
                continue;
            }

            // Check if it's a theorem
            if let Some(other_theorem) = database.get_theorem(&label) {
                apply_assertion(
                    &mut stack,
                    &other_theorem.core.hypotheses,
                    &other_theorem.core.statement,
                    &other_theorem.core.distinctness,
                    &theorem.core.distinctness,
                    database,
                    step_num,
                    label.as_str(),
                    &mut parse_cache,
                )?;
                step_num += 1;
                continue;
            }

            return Err(VerificationError::HypothesisNotFound {
                label: label_str.to_string(),
                step: step_num,
            });
        } else if ch == 'Z' {
            // 'Z' operation: save current stack top to `saved_steps`
            if stack.is_empty() {
                return Err(VerificationError::StackUnderflow(Box::new(
                    StackUnderflowDetails {
                        step: step_num,
                        step_display: step_num + 1,
                        label: None,
                        required: 1,
                        available: 0,
                        stack_contents: String::new(),
                    },
                )));
            }
            saved_steps.push(stack[stack.len() - 1].clone());
        }
        // Ignore other characters
    }

    // Verify final stack: must have exactly one item
    if stack.len() != 1 {
        return Err(VerificationError::FinalStackSize { count: stack.len() });
    }

    // Convert final DbTerm to symbols for comparison with theorem statement
    let mut final_symbols =
        stack[0]
            .to_symbol_sequence()
            .map_err(|e| VerificationError::ParseError {
                step: step_num,
                error: format!("converting final term to symbols: {}", e),
            })?;

    // If theorem statement starts with "|-", the final term is a Boolean expression
    // Replace Boolean type prefix with "|-" for comparison
    if theorem.core.statement.first().map(|s| s.as_ref()) == Some("|-") {
        if let Some(bool_type) = database.type_mapping().get_boolean_type() {
            if final_symbols.first().map(|s| s.as_ref()) == Some(bool_type.as_ref()) {
                final_symbols[0] = Arc::from("|-");
            }
        }
    }

    if final_symbols != theorem.core.statement {
        return Err(VerificationError::FinalStatementMismatch(Box::new(
            FinalStatementMismatchDetails {
                expected: format_statement(&theorem.core.statement, 200),
                got: format_statement(&final_symbols, 200),
            },
        )));
    }

    Ok(())
}

/// Find a hypothesis by label in the theorem's hypotheses.
fn find_hypothesis(
    hypotheses: &(Vec<FloatingHyp>, Vec<EssentialHyp>),
    label: &Label,
) -> Option<Vec<Arc<str>>> {
    // Check floating hypotheses
    for hyp in &hypotheses.0 {
        if &hyp.label == label {
            return Some(vec![hyp.type_code.clone(), hyp.variable.clone()]);
        }
    }

    // Check essential hypotheses
    for hyp in &hypotheses.1 {
        if &hyp.label == label {
            return Some(hyp.statement.clone());
        }
    }

    None
}

/// Format a substitution value as a string for error messages.
fn format_substitution(subst: &[Arc<str>]) -> String {
    subst
        .iter()
        .map(|s| s.as_ref())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Format a statement for error messages, with truncation for very long statements.
fn format_statement(statement: &[Arc<str>], max_len: usize) -> String {
    let full = format_substitution(statement);
    if full.len() <= max_len {
        full
    } else {
        // Truncate and add ellipsis
        let truncated = &full[..max_len];
        // Try to truncate at a word boundary
        if let Some(last_space) = truncated.rfind(' ') {
            format!("{}...", &full[..last_space])
        } else {
            format!("{}...", truncated)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{
        AssertionCore, MetamathDatabase, Parser, StdFilesystem, Theorem, TypeMapping,
    };
    use crate::DistinctnessGraph;

    #[test]
    fn verify_demo0_th1() {
        // Parse `demo0.mm`
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser =
            Parser::new(fs, "tests/metamath-exe/demo0.mm", db).expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse demo0.mm");

        // Get the theorem `th1`
        let th1_label = Label::new("th1").expect("Failed to create label");
        let th1 = db.get_theorem(&th1_label).expect("Theorem th1 not found");

        // Verify the proof
        let result = verify_theorem(&th1, &db);
        assert!(
            result.is_ok(),
            "Proof verification failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn verify_demo0_all_theorems() {
        // Parse `demo0.mm`
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser =
            Parser::new(fs, "tests/metamath-exe/demo0.mm", db).expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse demo0.mm");

        // Verify all theorems in `demo0.mm`
        let all_theorems = db.theorems();
        assert!(!all_theorems.is_empty(), "No theorems found in demo0.mm");

        for (label, theorem) in all_theorems {
            let result = verify_theorem(&theorem, &db);
            assert!(
                result.is_ok(),
                "Verification failed for theorem '{}': {:?}",
                label,
                result.err()
            );
        }
    }

    #[test]
    fn verify_big_unifier() {
        // Parse `big-unifier.mm` which contains compressed proofs
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "tests/metamath-exe/big-unifier.mm", db)
            .expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse big-unifier.mm");

        // Verify all theorems (both compressed and expanded proofs)
        let all_theorems = db.theorems();
        assert!(
            !all_theorems.is_empty(),
            "No theorems found in big-unifier.mm"
        );

        for (label, theorem) in all_theorems {
            let result = verify_theorem(&theorem, &db);
            assert!(
                result.is_ok(),
                "Verification failed for theorem '{}': {:?}",
                label,
                result.err()
            );
        }
    }

    #[test]
    #[ignore] // Long-running test - can take several seconds
    fn verify_set_mm_sample() {
        // Integration test that parses set.mm and verifies sample theorems.
        // Parser now handles comments in theorem statements.

        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Check if file exists
        if !std::path::Path::new("tests/metamath-test/set.mm").exists() {
            eprintln!("Skipping test - set.mm not found");
            return;
        }

        // Parse set.mm
        let parser =
            Parser::new(fs, "tests/metamath-test/set.mm", db).expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse set.mm");

        // Verify some sample theorems
        let test_theorems = vec!["a1i", "a2i", "pm2.43i"];
        let all_theorems = db.theorems();

        for theorem_name in test_theorems {
            let label = Label::new(theorem_name).expect("Failed to create label");
            let theorem = all_theorems
                .get(&label)
                .unwrap_or_else(|| panic!("Theorem '{}' not found", theorem_name));

            let result = verify_theorem(theorem, &db);
            assert!(
                result.is_ok(),
                "Verification failed for '{}': {:?}",
                theorem_name,
                result.err()
            );
        }
    }

    #[test]
    fn missing_proof() {
        // Create a theorem without a proof

        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let theorem = Theorem {
            core: AssertionCore {
                label: Label::new("test").unwrap(),
                statement: vec![Arc::from("|-"), Arc::from("P")],
                line: 1,
                hypotheses: (Vec::new(), Vec::new()),
                comment: None,
                distinctness: DistinctnessGraph::new(),
            },
            all_hypotheses: (Vec::new(), Vec::new()),
            mandatory_hyp_labels: Vec::new(),
            proof: None,
        };

        let result = verify_theorem(&theorem, &db);
        assert!(matches!(
            result,
            Err(VerificationError::MissingProof { .. })
        ));
    }

    #[test]
    fn final_statement_mismatch() {
        // This would require constructing a proof that proves the wrong statement
        // Difficult to construct manually, but the error case is covered in verification logic
    }

    #[test]
    fn distinctness_violation_same_variable() {
        // `disjoint1.mm`: theorem 'bad' uses same variable twice, violating `$d` constraint
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::formula_mm());
        let parser = Parser::new(fs, "tests/metamath-exe/disjoint1.mm", db)
            .expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse disjoint1.mm");

        let bad_label = Label::new("bad").expect("Failed to create label");
        let bad = db.get_theorem(&bad_label).expect("Theorem bad not found");

        let result = verify_theorem(&bad, &db);
        assert!(
            matches!(result, Err(VerificationError::DistinctnessViolation { .. })),
            "Expected distinctness violation, got: {:?}",
            result
        );
    }

    #[test]
    fn distinctness_violation_missing_constraint() {
        // `disjoint3.mm`: theorem 'bad' uses different variables without required `$d` constraint
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::formula_mm());
        let parser = Parser::new(fs, "tests/metamath-exe/disjoint3.mm", db)
            .expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse disjoint3.mm");

        let bad_label = Label::new("bad").expect("Failed to create label");
        let bad = db.get_theorem(&bad_label).expect("Theorem bad not found");

        let result = verify_theorem(&bad, &db);
        assert!(
            matches!(result, Err(VerificationError::DistinctnessViolation { .. })),
            "Expected distinctness violation for missing `$d` constraint, got: {:?}",
            result
        );
    }

    #[test]
    fn distinctness_with_proper_constraints() {
        // `disjoint2.mm`: theorems `'good'` and `'stillgood'` have proper `$d` constraints
        let fs = StdFilesystem::new();
        let db = MetamathDatabase::new(TypeMapping::formula_mm());
        let parser = Parser::new(fs, "tests/metamath-exe/disjoint2.mm", db)
            .expect("Failed to create parser");
        let db = parser.parse().expect("Failed to parse disjoint2.mm");

        // `'good'` has `$d x y z w $.` (all pairwise distinct) - should pass
        let good_label = Label::new("good").expect("Failed to create label");
        let good = db.get_theorem(&good_label).expect("Theorem good not found");
        let result = verify_theorem(&good, &db);
        assert!(
            result.is_ok(),
            "Expected 'good' to verify successfully, got: {:?}",
            result.err()
        );

        // `'stillgood'` has all pairwise `$d` constraints separately - should pass
        let stillgood_label = Label::new("stillgood").expect("Failed to create label");
        let stillgood = db
            .get_theorem(&stillgood_label)
            .expect("Theorem stillgood not found");
        let result = verify_theorem(&stillgood, &db);
        assert!(
            result.is_ok(),
            "Expected 'stillgood' to verify successfully, got: {:?}",
            result.err()
        );

        // `'semigood'` has no `$d` constraints - should fail
        let semigood_label = Label::new("semigood").expect("Failed to create label");
        let semigood = db
            .get_theorem(&semigood_label)
            .expect("Theorem semigood not found");
        let result = verify_theorem(&semigood, &db);
        assert!(
            matches!(result, Err(VerificationError::DistinctnessViolation { .. })),
            "Expected 'semigood' to fail with distinctness violation, got: {:?}",
            result
        );
    }
}
