//! Metamath expression parser.
//!
//! This module provides functions to parse Metamath expressions (symbol sequences)
//! into `DbTerm` instances for use with symbolic-mgu's unification operations.

use crate::metamath::database::MetamathDatabase;
use crate::metamath::pattern::{PatternElement, SyntaxAxiomPattern};
use crate::metamath::symbolic::{DbMetavariableFactory, DbNode, DbTerm};
use crate::{EnumTermFactory, MetavariableFactory, MguError, TermFactory};
use std::sync::Arc;

/// Parse a Metamath expression to `DbTerm`.
///
/// # Metamath Expression Format
///
/// Metamath expressions are sequences like:
/// - `["wff", "ph"]` - a variable
/// - `["wff", "(", "ph", "->", "ps", ")"]` - implication
/// - `["|-", "(", "ph", "->", "ps", ")"]` - assertion of implication
///
/// # Arguments
///
/// * `symbols` - The symbol sequence from Metamath
/// * `db_arc` - Database reference for variable/constant lookups
///
/// # Returns
///
/// A `DbTerm` representing the expression.
///
/// # Errors
///
/// Returns `MguError` if:
/// - Empty symbol vector
/// - Type code not recognized
/// - Unknown symbol (not a variable or constant)
/// - Malformed expression (wrong arity, unmatched pattern, etc.)
pub fn parse_expression(
    symbols: &[Arc<str>],
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError> {
    if symbols.is_empty() {
        return Err(MguError::ParseError {
            location: "expression".to_string(),
            message: "Empty symbol sequence".to_string(),
        });
    }

    // Extract type code (first symbol)
    let type_code = &symbols[0];

    // Extract sequence (remaining symbols)
    let sequence = &symbols[1..];

    // Parse the sequence
    parse_sequence(sequence, type_code, db_arc)
}

/// Recursively parse a symbol sequence with a given expected type.
///
/// This function is public to allow `AssertionCore::to_statement()` to parse
/// assertion statements by skipping the "|-" prefix and parsing the rest as Boolean.
///
/// # Errors
///
/// Returns `MguError` if:
/// - No syntax axioms are defined for the given type code
/// - The sequence doesn't match any syntax axiom pattern
/// - Variable subsequences cannot be parsed recursively
/// - The pattern matching fails (constants don't match, etc.)
pub fn parse_sequence(
    sequence: &[Arc<str>],
    type_code: &Arc<str>,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError> {
    // Case 1: Single symbol - could be a variable
    if sequence.len() == 1 {
        let symbol = &sequence[0];

        // Check floating hypothesis: `(type_code, symbol)` → hypothesis
        if let Some(_float_hyp) = db_arc.lookup_floating_hyp(type_code, symbol) {
            // It's a variable bound to this type
            let var_factory = DbMetavariableFactory::new(Arc::clone(db_arc));
            let var = var_factory.create_by_name(symbol)?;
            let term_factory = EnumTermFactory::new();
            return term_factory.create_leaf(var);
        }

        // Not a variable - fall through to pattern matching
    }

    // Case 2: Pattern matching against syntax axioms
    let candidates = db_arc.get_syntax_axioms_for_type(type_code);

    if candidates.is_empty() {
        return Err(MguError::ParseError {
            location: "expression".to_string(),
            message: format!("No syntax axioms defined for type '{}'", type_code),
        });
    }

    // Filter candidates by pattern hints
    let matches = filter_patterns(sequence, &candidates)?;

    if matches.is_empty() {
        return Err(MguError::ParseError {
            location: "expression".to_string(),
            message: format!(
                "No syntax axiom of type '{}' matches sequence: {:?}",
                type_code, sequence
            ),
        });
    }

    // Handle ambiguity per nuniq-gram.mm:
    // Multiple matches are allowed as long as they derive the same syntax theorem.
    // For our purposes (parsing expressions in context), we use the first match.
    if matches.len() > 1 {
        eprintln!(
            "Warning: Ambiguous parse for type '{}', sequence {:?}. Using axiom '{}'.",
            type_code, sequence, matches[0].label
        );
    }

    let pattern = &matches[0];
    parse_with_pattern(sequence, pattern, db_arc)
}

/// Filter patterns by structural hints (fast elimination).
///
/// Returns patterns that could potentially match the sequence.
fn filter_patterns(
    sequence: &[Arc<str>],
    candidates: &[SyntaxAxiomPattern],
) -> Result<Vec<SyntaxAxiomPattern>, MguError> {
    let mut matches = Vec::new();

    for pattern in candidates {
        // Check first constant
        if let Some(first_const) = &pattern.hints.first_constant {
            if sequence.is_empty() || &sequence[0] != first_const {
                continue; // Eliminate
            }
        }

        // Check last constant
        if let Some(last_const) = &pattern.hints.last_constant {
            if sequence.is_empty() || sequence.last() != Some(last_const) {
                continue; // Eliminate
            }
        }

        // Check constants appear in order
        if !constants_in_order(sequence, &pattern.hints.constants_in_order) {
            continue; // Eliminate
        }

        // Check adjacent constants
        if !has_adjacent_pairs(sequence, &pattern.hints.adjacent_constants) {
            continue; // Eliminate
        }

        // Survived all filters - candidate match
        matches.push(pattern.clone());
    }

    Ok(matches)
}

/// Check if constants appear in sequence in the specified order.
fn constants_in_order(sequence: &[Arc<str>], required_constants: &[Arc<str>]) -> bool {
    let mut const_index = 0;
    for symbol in sequence {
        if const_index < required_constants.len() && symbol == &required_constants[const_index] {
            const_index += 1;
        }
    }
    const_index == required_constants.len()
}

/// Check if all required adjacent constant pairs appear in sequence.
fn has_adjacent_pairs(sequence: &[Arc<str>], required_pairs: &[(Arc<str>, Arc<str>)]) -> bool {
    for (first, second) in required_pairs {
        let mut found = false;
        for window in sequence.windows(2) {
            if &window[0] == first && &window[1] == second {
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

/// Parse sequence using a matched pattern.
fn parse_with_pattern(
    sequence: &[Arc<str>],
    pattern: &SyntaxAxiomPattern,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError> {
    // Extract variable subsequences from sequence using pattern
    let var_sequences = extract_variables(sequence, &pattern.pattern, db_arc)?;

    // Recursively parse each variable's sequence
    let mut children = Vec::new();
    for (var_type, var_seq) in var_sequences {
        let child = parse_sequence(&var_seq, &var_type, db_arc)?;
        children.push(child);
    }

    // Build the node
    let node = DbNode::new(pattern.label.clone(), Arc::clone(db_arc));
    let factory = EnumTermFactory::new();
    factory.create_node(node, children)
}

/// Type alias for variable extraction results: `(type_code, symbol_sequence)`
type VarExtraction = Vec<(Arc<str>, Vec<Arc<str>>)>;

/// Extract variable subsequences from sequence using pattern.
///
/// This is the core pattern matching logic. It uses recursive descent with backtracking
/// to handle ambiguous boundaries in nested expressions.
///
/// # Algorithm
///
/// For each pattern element:
/// - **Constant**: Must match at current position, otherwise fail
/// - **Variable**: Try all possible lengths, recursively parsing each candidate
///   - For each length, parse the subsequence with the variable's type
///   - If successful, try to match the rest of the pattern
///   - If rest fails, backtrack and try next length
///   - First successful parse wins
///
/// # Examples
///
/// ```text
/// Pattern: [C("("), V{class}, C("+"), V{class}, C(")")]
/// Sequence: ["(", "(", "A", "+", "B", ")", "+", "(", "C", "+", "D", ")", ")"]
///
/// Tries:
///   V1=["("] → doesn't parse as class
///   V1=["(","A"] → doesn't parse as class
///   ...
///   V1=["(","A","+","B",")"] → parses! Next is "+", matches pattern, continue...
/// ```
fn extract_variables(
    sequence: &[Arc<str>],
    pattern: &[PatternElement],
    db_arc: &Arc<MetamathDatabase>,
) -> Result<VarExtraction, MguError> {
    // Use backtracking algorithm
    try_extract(sequence, pattern, 0, 0, Vec::new(), db_arc)
}

/// Recursive helper for pattern matching with backtracking.
///
/// # Arguments
///
/// * `sequence` - The full symbol sequence to match
/// * `pattern` - The full pattern to match against
/// * `seq_idx` - Current position in sequence
/// * `pat_idx` - Current position in pattern
/// * `accumulated_vars` - Variables extracted so far
/// * `db_arc` - Database for recursive parsing
///
/// # Returns
///
/// The complete variable extraction on success, or an error describing the failure.
fn try_extract(
    sequence: &[Arc<str>],
    pattern: &[PatternElement],
    seq_idx: usize,
    pat_idx: usize,
    accumulated_vars: VarExtraction,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<VarExtraction, MguError> {
    // Base case: finished the pattern
    if pat_idx == pattern.len() {
        if seq_idx == sequence.len() {
            // Successfully consumed entire sequence
            return Ok(accumulated_vars);
        } else {
            // Pattern exhausted but sequence has leftover symbols
            return Err(MguError::ParseError {
                location: "expression".to_string(),
                message: format!(
                    "Pattern matching did not consume entire sequence: {} of {} symbols used",
                    seq_idx,
                    sequence.len()
                ),
            });
        }
    }

    // Process current pattern element
    match &pattern[pat_idx] {
        PatternElement::Constant(const_sym) => {
            // Must match at current position
            if seq_idx >= sequence.len() {
                return Err(MguError::ParseError {
                    location: "expression".to_string(),
                    message: format!(
                        "Pattern mismatch: expected '{}' at position {}, but sequence ended",
                        const_sym, seq_idx
                    ),
                });
            }

            if &sequence[seq_idx] != const_sym {
                return Err(MguError::ParseError {
                    location: "expression".to_string(),
                    message: format!(
                        "Pattern mismatch: expected '{}' at position {}, found '{}'",
                        const_sym, seq_idx, sequence[seq_idx]
                    ),
                });
            }

            // Match successful, continue with next pattern element
            try_extract(
                sequence,
                pattern,
                seq_idx + 1,
                pat_idx + 1,
                accumulated_vars,
                db_arc,
            )
        }

        PatternElement::Variable { type_code, .. } => {
            // Try all possible lengths for this variable
            let remaining = sequence.len() - seq_idx;

            if remaining == 0 {
                return Err(MguError::ParseError {
                    location: "expression".to_string(),
                    message: format!(
                        "Variable at pattern position {} has empty sequence",
                        pat_idx
                    ),
                });
            }

            // Try lengths from 1 to remaining, using first successful parse
            for length in 1..=remaining {
                let candidate = &sequence[seq_idx..seq_idx + length];

                // Try to parse this candidate as the required type
                if let Ok(_term) = parse_sequence(candidate, type_code, db_arc) {
                    // This length parses successfully as the required type
                    // Try to match the rest of the pattern
                    let mut new_vars = accumulated_vars.clone();
                    new_vars.push((type_code.clone(), candidate.to_vec()));

                    if let Ok(result) = try_extract(
                        sequence,
                        pattern,
                        seq_idx + length,
                        pat_idx + 1,
                        new_vars,
                        db_arc,
                    ) {
                        // Success! This is the correct parse
                        return Ok(result);
                    }

                    // Rest of pattern didn't match, backtrack and try next length
                }
            }

            // No valid length found for this variable
            Err(MguError::ParseError {
                location: "expression".to_string(),
                message: format!(
                    "No valid parse found for variable at pattern position {} (type '{}')",
                    pat_idx, type_code
                ),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::database::{AssertionCore, TypeMapping};
    use crate::metamath::label::Label;
    use crate::DistinctnessGraph;
    use std::collections::HashSet;

    fn setup_test_db() -> Arc<MetamathDatabase> {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        // Register constants
        db.register_constant_symbol(Arc::from("wff")).unwrap();
        db.register_constant_symbol(Arc::from("(")).unwrap();
        db.register_constant_symbol(Arc::from("->")).unwrap();
        db.register_constant_symbol(Arc::from(")")).unwrap();

        // Register variables
        db.register_variable_symbol(Arc::from("ph")).unwrap();
        db.register_variable_symbol(Arc::from("ps")).unwrap();

        // Register variable types
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();

        // Add floating hypotheses
        db.add_floating_hyp(crate::metamath::database::FloatingHyp {
            label: Label::new("wph").unwrap(),
            variable: Arc::from("ph"),
            type_code: Arc::from("wff"),
            line: 1,
        })
        .unwrap();

        db.add_floating_hyp(crate::metamath::database::FloatingHyp {
            label: Label::new("wps").unwrap(),
            variable: Arc::from("ps"),
            type_code: Arc::from("wff"),
            line: 2,
        })
        .unwrap();

        db
    }

    fn create_implication_axiom(db: &Arc<MetamathDatabase>) {
        use crate::metamath::database::Axiom;

        // Create implication syntax axiom: `wi $a wff ( ph -> ps ) $.`
        let statement = vec![
            Arc::from("wff"),
            Arc::from("("),
            Arc::from("ph"),
            Arc::from("->"),
            Arc::from("ps"),
            Arc::from(")"),
        ];

        let active_vars: HashSet<Arc<str>> =
            vec![Arc::from("ph"), Arc::from("ps")].into_iter().collect();

        let syntax_info = crate::metamath::database::SyntaxInfo::from_statement(
            &statement,
            &active_vars,
            db.type_mapping(),
        )
        .expect("Should be a syntax axiom");

        let axiom = Axiom {
            core: AssertionCore {
                label: Label::new("wi").unwrap(),
                statement,
                line: 1,
                hypotheses: (Vec::new(), Vec::new()),
                comment: None,
                distinctness: DistinctnessGraph::new(),
            },
            type_code: Arc::from("wff"),
            syntax_info: Some(syntax_info.clone()),
        };

        // Index the axiom
        db.index_syntax_axiom(&axiom);

        // Also add it to the axioms map
        db.add_axiom(axiom).unwrap();
    }

    #[test]
    fn parse_simple_variable() {
        let db = setup_test_db();

        // Parse: ["wff", "ph"]
        let symbols = vec![Arc::from("wff"), Arc::from("ph")];
        let term = parse_expression(&symbols, &db).unwrap();

        // Should be a metavariable
        use crate::Term;
        assert!(term.is_metavariable());
    }

    #[test]
    fn parse_implication() {
        let db = setup_test_db();
        create_implication_axiom(&db);

        // Parse: ["wff", "(", "ph", "->", "ps", ")"]
        let symbols = vec![
            Arc::from("wff"),
            Arc::from("("),
            Arc::from("ph"),
            Arc::from("->"),
            Arc::from("ps"),
            Arc::from(")"),
        ];
        let term = parse_expression(&symbols, &db).unwrap();

        // Should be a node (not a metavariable)
        use crate::Term;
        assert!(!term.is_metavariable());

        // Should have 2 children
        assert_eq!(term.get_n_children(), 2);
    }

    #[test]
    fn parse_error_empty_sequence() {
        let db = setup_test_db();

        let symbols = vec![];
        let result = parse_expression(&symbols, &db);

        assert!(result.is_err());
    }

    #[test]
    fn parse_error_unknown_symbol() {
        let db = setup_test_db();

        // Parse: ["wff", "unknown"]
        let symbols = vec![Arc::from("wff"), Arc::from("unknown")];
        let result = parse_expression(&symbols, &db);

        assert!(result.is_err());
    }
}
