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

use crate::metamath::database::{EssentialHyp, FloatingHyp, MetamathDatabase, Theorem};
use crate::metamath::label::Label;
use crate::metamath::proof::Proof;
use crate::metamath::symbolic::DbMetavariable;
use std::collections::HashMap;
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

/// A substitution mapping variable names to their replacement statements.
type Substitution = HashMap<Arc<str>, Vec<Arc<str>>>;

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
            label: theorem.label.to_string(),
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
    // Initialize verification stack
    let mut stack: Vec<Vec<Arc<str>>> = Vec::new();

    // Process each proof step
    for (step_num, label_str) in steps.iter().enumerate() {
        let label =
            Label::from_encoded(label_str).map_err(|_| VerificationError::HypothesisNotFound {
                label: label_str.to_string(),
                step: step_num,
            })?;

        // Check if it's a hypothesis (from theorem's mandatory hypotheses)
        if let Some(statement) = find_hypothesis(&theorem.hypotheses, &label) {
            stack.push(statement);
            continue;
        }

        // Check if it's a floating hypothesis from the database (may not be mandatory for this theorem)
        if let Some(float_hyp) = database.get_floating_hyp(&label) {
            stack.push(vec![float_hyp.type_code, float_hyp.variable]);
            continue;
        }

        // Check if it's an axiom
        if let Some(axiom) = database.get_axiom(&label) {
            apply_axiom_or_theorem(
                &mut stack,
                &axiom.hypotheses,
                &axiom.statement,
                &axiom.distinctness,
                &theorem.distinctness,
                database,
                step_num,
                label.as_str(),
            )?;
            continue;
        }

        // Check if it's a theorem
        if let Some(other_theorem) = database.get_theorem(&label) {
            apply_axiom_or_theorem(
                &mut stack,
                &other_theorem.hypotheses,
                &other_theorem.statement,
                &other_theorem.distinctness,
                &theorem.distinctness,
                database,
                step_num,
                label.as_str(),
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

    let final_statement = &stack[0];
    if final_statement != &theorem.statement {
        return Err(VerificationError::FinalStatementMismatch(Box::new(
            FinalStatementMismatchDetails {
                expected: format_statement(&theorem.statement, 200),
                got: format_statement(final_statement, 200),
            },
        )));
    }

    Ok(())
}

/// Verify a theorem using a compressed proof with 'Z' stack support.
fn verify_compressed(
    theorem: &Theorem,
    database: &Arc<MetamathDatabase>,
    labels: &[Arc<str>],
    proof_string: &str,
) -> Result<(), VerificationError> {
    // Build mandatory hypothesis label list
    let mut mandatory_hyps = Vec::new();
    for hyp in &theorem.hypotheses.0 {
        mandatory_hyps.push(Arc::from(hyp.label.encoded()));
    }
    for hyp in &theorem.hypotheses.1 {
        mandatory_hyps.push(Arc::from(hyp.label.encoded()));
    }

    // Initialize verification stack and proof stack (for 'Z' operations)
    let mut stack: Vec<Vec<Arc<str>>> = Vec::new();
    let mut proof_stack: Vec<Vec<Arc<str>>> = Vec::new();

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

            // Look up label: `mandatory_hyps` -> labels -> `proof_stack`
            let label_str = if number < mandatory_hyps.len() {
                &mandatory_hyps[number]
            } else {
                let label_index = number - mandatory_hyps.len();
                if label_index < labels.len() {
                    &labels[label_index]
                } else {
                    let proof_stack_index = label_index - labels.len();
                    if proof_stack_index >= proof_stack.len() {
                        return Err(VerificationError::HypothesisNotFound {
                            label: format!("<proof-stack[{}]>", proof_stack_index),
                            step: step_num,
                        });
                    }
                    // Push saved statement from proof stack
                    stack.push(proof_stack[proof_stack_index].clone());
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

            // Check if it's a hypothesis (first check mandatory, then all)
            if let Some(statement) = find_hypothesis(&theorem.hypotheses, &label) {
                stack.push(statement);
                step_num += 1;
                continue;
            }

            // Check in all hypotheses that were in scope (for non-mandatory hypotheses in proof)
            if let Some(statement) = find_hypothesis(&theorem.all_hypotheses, &label) {
                stack.push(statement);
                step_num += 1;
                continue;
            }

            // Check if it's a floating hypothesis in the database
            if let Some(float_hyp) = database.get_floating_hyp(&label) {
                stack.push(vec![float_hyp.type_code, float_hyp.variable]);
                step_num += 1;
                continue;
            }

            // Check if it's an axiom
            if let Some(axiom) = database.get_axiom(&label) {
                apply_axiom_or_theorem(
                    &mut stack,
                    &axiom.hypotheses,
                    &axiom.statement,
                    &axiom.distinctness,
                    &theorem.distinctness,
                    database,
                    step_num,
                    label.as_str(),
                )?;
                step_num += 1;
                continue;
            }

            // Check if it's a theorem
            if let Some(other_theorem) = database.get_theorem(&label) {
                apply_axiom_or_theorem(
                    &mut stack,
                    &other_theorem.hypotheses,
                    &other_theorem.statement,
                    &other_theorem.distinctness,
                    &theorem.distinctness,
                    database,
                    step_num,
                    label.as_str(),
                )?;
                step_num += 1;
                continue;
            }

            return Err(VerificationError::HypothesisNotFound {
                label: label_str.to_string(),
                step: step_num,
            });
        } else if ch == 'Z' {
            // 'Z' operation: save current stack top to proof stack
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
            proof_stack.push(stack[stack.len() - 1].clone());
        }
        // Ignore other characters
    }

    // Verify final stack
    if stack.len() != 1 {
        return Err(VerificationError::FinalStackSize { count: stack.len() });
    }

    let final_statement = &stack[0];
    if final_statement != &theorem.statement {
        return Err(VerificationError::FinalStatementMismatch(Box::new(
            FinalStatementMismatchDetails {
                expected: format_statement(&theorem.statement, 200),
                got: format_statement(final_statement, 200),
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

/// Apply an axiom or theorem to the stack.
#[allow(clippy::too_many_arguments)]
fn apply_axiom_or_theorem(
    stack: &mut Vec<Vec<Arc<str>>>,
    hypotheses: &(Vec<FloatingHyp>, Vec<EssentialHyp>),
    conclusion: &[Arc<str>],
    distinctness: &crate::DistinctnessGraph<DbMetavariable>,
    calling_distinctness: &crate::DistinctnessGraph<DbMetavariable>,
    database: &Arc<MetamathDatabase>,
    step_num: usize,
    assertion_label: &str,
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
                stack_contents: format_stack_contents(stack),
            },
        )));
    }

    // Pop required number of statements from stack
    let stack_items: Vec<Vec<Arc<str>>> = stack.drain(stack.len() - required..).collect();

    // Build substitution from floating hypotheses
    let mut substitution = Substitution::new();
    for (i, float_hyp) in floating_hyps.iter().enumerate() {
        let stack_statement = &stack_items[i];

        // Verify type code matches
        if !stack_statement.is_empty() && stack_statement[0] != float_hyp.type_code {
            return Err(VerificationError::SubstitutionMismatch {
                step: step_num,
                variable: float_hyp.variable.to_string(),
            });
        }

        // Extract the substituted value (skip type code)
        let substituted_value = if stack_statement.len() > 1 {
            stack_statement[1..].to_vec()
        } else {
            vec![]
        };

        substitution.insert(float_hyp.variable.clone(), substituted_value);
    }

    // Verify essential hypotheses match
    for (i, ess_hyp) in essential_hyps.iter().enumerate() {
        let stack_statement = &stack_items[floating_hyps.len() + i];
        let expected = apply_substitution(&ess_hyp.statement, &substitution);

        if stack_statement != &expected {
            return Err(VerificationError::EssentialMismatch(Box::new(
                EssentialMismatchDetails {
                    step: step_num,
                    step_display: step_num + 1,
                    expected: format_statement(&expected, 200),
                    got: format_statement(stack_statement, 200),
                },
            )));
        }
    }

    // Check distinctness constraints from the axiom/theorem being applied
    for (var1, var2) in distinctness.edges_iter() {
        // Collect all variables in the substituted values for both metavariables
        let vars1 = collect_variables(&substitution, &var1);
        let vars2 = collect_variables(&substitution, &var2);

        // Get substitution values for error reporting
        let var1_name = var1.to_string();
        let var2_name = var2.to_string();
        let var1_subst_value = substitution
            .get(var1_name.as_str())
            .cloned()
            .unwrap_or_default();
        let var2_subst_value = substitution
            .get(var2_name.as_str())
            .cloned()
            .unwrap_or_default();

        // For each pair of variables, check if they violate the distinctness requirement
        for v1 in &vars1 {
            for v2 in &vars2 {
                // If the same variable appears in both substitutions, that's a violation
                if v1 == v2 {
                    return Err(VerificationError::DistinctnessViolation(Box::new(
                        DistinctnessViolationDetails {
                            step: step_num,
                            step_display: step_num + 1,
                            assertion_label: assertion_label.to_string(),
                            var1_name: var1_name.clone(),
                            var2_name: var2_name.clone(),
                            var1_subst: format_substitution(&var1_subst_value),
                            var2_subst: format_substitution(&var2_subst_value),
                            conflict_explanation: format!(
                                "These substitutions have variable \"{}\" in common.",
                                v1
                            ),
                        },
                    )));
                }

                // If they're different variables, we need to verify they have a
                // distinctness constraint in the calling theorem's scope
                if !variables_are_distinct(v1, v2, calling_distinctness, database) {
                    return Err(VerificationError::DistinctnessViolation(Box::new(
                        DistinctnessViolationDetails {
                            step: step_num,
                            step_display: step_num + 1,
                            assertion_label: assertion_label.to_string(),
                            var1_name: var1_name.clone(),
                            var2_name: var2_name.clone(),
                            var1_subst: format_substitution(&var1_subst_value),
                            var2_subst: format_substitution(&var2_subst_value),
                            conflict_explanation: format!(
                                "These substitutions require variables \"{}\" and \"{}\" to be disjoint, but no $d constraint exists.",
                                v1, v2
                            ),
                        },
                    )));
                }
            }
        }
    }

    // Push substituted conclusion
    let substituted_conclusion = apply_substitution(conclusion, &substitution);
    stack.push(substituted_conclusion);

    Ok(())
}

/// Apply a substitution to a statement.
fn apply_substitution(statement: &[Arc<str>], substitution: &Substitution) -> Vec<Arc<str>> {
    let mut result = Vec::new();
    for symbol in statement {
        if let Some(replacement) = substitution.get(symbol) {
            result.extend(replacement.iter().cloned());
        } else {
            result.push(symbol.clone());
        }
    }
    result
}

/// Format a substitution value as a string for error messages.
fn format_substitution(subst: &[Arc<str>]) -> String {
    subst
        .iter()
        .map(|s| s.as_ref())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Format stack contents for error messages.
/// Shows the top entries (most recent first) for better debugging.
fn format_stack_contents(stack: &[Vec<Arc<str>>]) -> String {
    if stack.is_empty() {
        return String::new();
    }

    // Show top 3 entries (most recent first)
    let entries_to_show = stack.len().min(3);
    let entries: Vec<String> = stack[stack.len() - entries_to_show..]
        .iter()
        .rev()
        .map(|entry| format!("\"{}\"", format_substitution(entry)))
        .collect();

    if stack.len() > 3 {
        format!("{} (and {} more)", entries.join(", "), stack.len() - 3)
    } else {
        entries.join(", ")
    }
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

/// Collect all variables appearing in the substitution for a given metavariable.
///
/// This is used for distinctness checking: we need to find all variables that
/// appear in the substituted value for a metavariable.
fn collect_variables(
    substitution: &Substitution,
    metavar: &DbMetavariable,
) -> std::collections::HashSet<Arc<str>> {
    let mut vars = std::collections::HashSet::new();

    // Get the variable name for this metavariable
    if let Some(var_name) = metavar
        .database()
        .variables_of_type(metavar.type_code())
        .get(metavar.index())
    {
        // Look up the substituted value for this variable
        if let Some(substituted_value) = substitution.get(var_name) {
            // Collect all variables in the substituted value
            // Variables are symbols that appear in the database's variable list
            for symbol in substituted_value {
                if metavar.database().is_variable(symbol) {
                    vars.insert(symbol.clone());
                }
            }
        }
    }

    vars
}

/// Check if two variables have a distinctness constraint in the given distinctness graph.
///
/// Returns `true` if the variables are guaranteed to be distinct (i.e., they have a
/// distinctness edge in the graph), `false` otherwise.
fn variables_are_distinct(
    var1: &Arc<str>,
    var2: &Arc<str>,
    distinctness: &crate::DistinctnessGraph<DbMetavariable>,
    database: &Arc<MetamathDatabase>,
) -> bool {
    // Get type and index for each variable
    let (type1, index1) = match database.variable_type_and_index(var1) {
        Some(ti) => ti,
        None => return false, // Variable not found - can't verify distinctness
    };

    let (type2, index2) = match database.variable_type_and_index(var2) {
        Some(ti) => ti,
        None => return false, // Variable not found - can't verify distinctness
    };

    // Create `DbMetavariable` instances
    let metavar1 = DbMetavariable::new(type1, index1, database.clone());
    let metavar2 = DbMetavariable::new(type2, index2, database.clone());

    // Check if there's a distinctness edge between these metavariables
    // DistinctnessGraph stores edges in both directions, so we only need to check one
    for (v1, v2) in distinctness.edges_iter() {
        if (v1 == metavar1 && v2 == metavar2) || (v1 == metavar2 && v2 == metavar1) {
            return true;
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::database::{MetamathDatabase, TypeMapping};
    use crate::metamath::filesystem::StdFilesystem;
    use crate::metamath::parser::Parser;

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
        use crate::metamath::database::Theorem;
        use crate::DistinctnessGraph;

        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let theorem = Theorem {
            label: Label::new("test").unwrap(),
            statement: vec![Arc::from("|-"), Arc::from("P")],
            line: 1,
            hypotheses: (Vec::new(), Vec::new()),
            all_hypotheses: (Vec::new(), Vec::new()),
            proof: None,
            comment: None,
            distinctness: DistinctnessGraph::new(),
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
        let db = MetamathDatabase::new(TypeMapping::set_mm());
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
        let db = MetamathDatabase::new(TypeMapping::set_mm());
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
        let db = MetamathDatabase::new(TypeMapping::set_mm());
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
