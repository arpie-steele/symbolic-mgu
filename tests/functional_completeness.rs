//! Tests for Boolean functional completeness.
//!
//! Verifies that minimal operator sets can generate all 16 two-variable Boolean functions
//! using the search module to enumerate terms up to a specified depth.
//!
//! # Performance Note
//!
//! Some tests ({¬, ∧} and {¬, ∨}) require deep searches (depth 4, ~850K terms).
//! For faster execution, run in release mode:
//!
//! ```bash
//! cargo test --release --test functional_completeness
//! ```
//!
//! # Test Structure
//!
//! Each test uses a parameterized helper function that:
//! 1. Creates terms using only the specified operators (via search module)
//! 2. Evaluates each term to get its 2-variable truth table (4-bit code 0-15)
//! 3. Collects unique truth functions in a HashSet
//! 4. Stops when all 16 functions are found (or max depth reached)
//!
//! # References
//!
//! - https://en.wikipedia.org/wiki/Functional_completeness
//! - 27 tests covering all minimal functionally complete operator sets:
//!   - 2 Sheffer functions: {NAND}, {NOR}
//!   - 18 two-operator sets: {¬, ∧}, {¬, ∨}, {→, ⊕}, etc.
//!   - 6 three-operator sets: {∨, ↔, ⊥}, {∧, ⊕, ⊤}, etc.

use std::collections::HashSet;
use symbolic_mgu::bool_eval::{BooleanSimpleNode, BooleanSimpleOp};
use symbolic_mgu::search::{get_iterator, TermSearchStaticState};
use symbolic_mgu::{
    EnumTerm, EnumTermFactory, MetavariableFactory, MguError, Node, SimpleType, SimpleTypeFactory,
    Term, WideMetavariable, WideMetavariableFactory,
};
use SimpleType::*;

type TestVar = WideMetavariable;
type TestNode = BooleanSimpleNode<SimpleType>;
type TestTerm = EnumTerm<SimpleType, TestVar, TestNode>;
type TestFactory = EnumTermFactory<SimpleType, TestVar, TestNode, SimpleTypeFactory>;

/// Recursively evaluate a Boolean term to get its complete truth table as a u8.
///
/// Uses the bool_eval module's parallel evaluation to compute all rows at once.
/// For 2 variables A and B:
/// - A's truth table is 0b1010 (true when A=1: rows 2,3)
/// - B's truth table is 0b1100 (true when B=1: rows 1,3)
///
/// Returns a 4-bit truth table where bit i represents the result for row i.
fn eval_bool_term_truth_table(
    term: &TestTerm,
    var_a: &TestVar,
    var_b: &TestVar,
) -> Result<u8, MguError> {
    if let Some(var) = term.get_metavariable() {
        // Variable - return its truth table
        if var == *var_a {
            Ok(0b1010u8) // A is true in rows 2,3 (binary: 10, 11)
        } else if var == *var_b {
            Ok(0b1100u8) // B is true in rows 1,3 (binary: 01, 11)
        } else {
            Err(MguError::BooleanEvaluationFailed {
                reason: format!("Unknown variable: {:?}", var),
            })
        }
    } else if let Some(node) = term.get_node() {
        let children: Vec<_> = term.get_children().collect();

        match node.to_boolean_op() {
            Some(BooleanSimpleOp::True0) => Ok(0b1111u8), // Always true
            Some(BooleanSimpleOp::False0) => Ok(0b0000u8), // Always false
            Some(op) => {
                // Recursively get truth tables for children
                let child_tables: Result<Vec<u8>, _> = children
                    .iter()
                    .map(|c| eval_bool_term_truth_table(c, var_a, var_b))
                    .collect();
                let child_tables = child_tables?;

                // Apply the operation to the truth tables using bool_eval's parallel evaluation
                match op.get_arity() {
                    0 => Err(MguError::BooleanEvaluationFailed {
                        reason: format!("Nullary operator {:?} should have been constant", op),
                    }),
                    1 if child_tables.len() == 1 => op
                        .eval1::<u8, u8, 2>(&child_tables[0])
                        .ok_or_else(|| MguError::BooleanEvaluationFailed {
                            reason: format!("eval1 failed for {:?}", op),
                        }),
                    2 if child_tables.len() == 2 => op
                        .eval2::<u8, u8, 2>(&child_tables[0], &child_tables[1])
                        .ok_or_else(|| MguError::BooleanEvaluationFailed {
                            reason: format!("eval2 failed for {:?}", op),
                        }),
                    _ => Err(MguError::BooleanEvaluationFailed {
                        reason: format!(
                            "Arity mismatch: op {:?} has arity {}, got {} children",
                            op,
                            op.get_arity(),
                            child_tables.len()
                        ),
                    }),
                }
            }
            None => Err(MguError::BooleanEvaluationFailed {
                reason: format!("Node is not a Boolean operation: {:?}", node),
            }),
        }
    } else {
        Err(MguError::BooleanEvaluationFailed {
            reason: "Term is neither variable nor node".to_string(),
        })
    }
}

/// Evaluate a 2-variable Boolean term to get its truth table as a 4-bit code (0-15).
///
/// Uses bool_eval's parallel evaluation to compute the entire truth table in one pass.
///
/// # Truth Table Encoding
///
/// For two Boolean variables A and B, the 4 possible input combinations are:
/// - Row 0: A=false, B=false → bit 0 (value 1)
/// - Row 1: A=false, B=true  → bit 1 (value 2)
/// - Row 2: A=true,  B=false → bit 2 (value 4)
/// - Row 3: A=true,  B=true  → bit 3 (value 8)
///
/// The result is the sum of bit values where the function outputs true.
///
/// # Examples
///
/// - False: 0b0000 = 0 (always false)
/// - AND:   0b1000 = 8 (true only when both true)
/// - OR:    0b1110 = 14 (false only when both false)
/// - True:  0b1111 = 15 (always true)
///
/// # Errors
///
/// Returns error if:
/// - Term is not Boolean type
/// - Term evaluation fails
/// - Term contains extra variables beyond A and B
fn evaluate_2var_truth_table(
    term: &TestTerm,
    var_a: &TestVar,
    var_b: &TestVar,
    _factory: &TestFactory,
) -> Result<u8, MguError> {
    // Evaluate the entire truth table in one parallel operation
    let truth_table = eval_bool_term_truth_table(term, var_a, var_b)?;

    // Mask to lower 4 bits (2 variables = 4 rows)
    Ok(truth_table & 0b1111)
}

/// Test functional completeness for a set of operators.
///
/// # Arguments
///
/// * `ops` - The set of BooleanSimpleOp operators to test
/// * `max_depth` - Maximum search depth (stops early if all 16 found)
///
/// # Returns
///
/// The depth at which all 16 functions were found, or max_depth if incomplete.
///
/// # Panics
///
/// Panics if not all 16 functions are found by max_depth.
fn test_functional_completeness(ops: &[BooleanSimpleOp], max_depth: usize) -> usize {
    let vf = WideMetavariableFactory::new(SimpleTypeFactory);
    let var_a = vf.list_metavariables_by_type(&Boolean).next().unwrap();
    let var_b = vf.list_metavariables_by_type(&Boolean).nth(1).unwrap();
    let vars = vec![var_a, var_b];

    // Convert operators to nodes
    let nodes: Vec<TestNode> = ops
        .iter()
        .map(|&op| BooleanSimpleNode::from_op(op, Boolean))
        .collect();

    // Create search state
    let tf = TestFactory::new(SimpleTypeFactory);
    let state =
        TermSearchStaticState::new(tf, &nodes, &vars).expect("Failed to create search state");

    let mut found_functions: HashSet<u8> = HashSet::new();

    // Search incrementally by depth
    for depth in 0..=max_depth {
        let iter = get_iterator(&state, Boolean, depth).expect("Failed to create iterator");

        let mut term_count = 0;
        for term in iter {
            term_count += 1;

            // Evaluate the term
            match evaluate_2var_truth_table(&term, &var_a, &var_b, state.get_term_factory()) {
                Ok(truth_code) => {
                    found_functions.insert(truth_code);
                }
                Err(_) => {
                    // Skip terms that don't evaluate cleanly
                    continue;
                }
            }

            // Early exit if we found all 16
            if found_functions.len() == 16 {
                eprintln!(
                    "  Depth {}: Found all 16 functions after {} terms",
                    depth, term_count
                );
                return depth;
            }
        }

        eprintln!(
            "  Depth {}: {} terms generated, {} functions found so far",
            depth,
            term_count,
            found_functions.len()
        );

        // Check if we're done after this depth
        if found_functions.len() == 16 {
            return depth;
        }
    }

    // Verify we found all 16
    assert_eq!(
        found_functions.len(),
        16,
        "Operator set {:?} did not generate all 16 Boolean functions by depth {}. Found {} functions: {:?}",
        ops,
        max_depth,
        found_functions.len(),
        {
            let mut sorted: Vec<u8> = found_functions.iter().copied().collect();
            sorted.sort();
            sorted
        }
    );

    max_depth
}

#[test]
fn sheffer_nand_is_functionally_complete() {
    eprintln!("\n=== Testing NAND functional completeness ===");
    let depth = test_functional_completeness(&[BooleanSimpleOp::NotAndAB2], 3);
    eprintln!("NAND: All 16 functions found by depth {}\n", depth);
    assert!(depth <= 5, "NAND should find all 16 functions by depth 5");
}

#[test]
fn sheffer_nor_is_functionally_complete() {
    eprintln!("\n=== Testing NOR functional completeness ===");
    let depth = test_functional_completeness(&[BooleanSimpleOp::NotOrAB2], 3);
    eprintln!("NOR: All 16 functions found by depth {}\n", depth);
    assert!(depth <= 5, "NOR should find all 16 functions by depth 5");
}

#[test]
fn sheffer_symmetry() {
    eprintln!("\n=== Testing NAND/NOR symmetry ===");
    // NAND and NOR should require the same depth due to De Morgan duality
    let nand_depth = test_functional_completeness(&[BooleanSimpleOp::NotAndAB2], 3);
    let nor_depth = test_functional_completeness(&[BooleanSimpleOp::NotOrAB2], 3);

    eprintln!("NAND depth: {}, NOR depth: {}\n", nand_depth, nor_depth);
    assert_eq!(
        nand_depth, nor_depth,
        "NAND and NOR should require the same depth due to De Morgan symmetry"
    );
}

// Two-operator sets (18 from Wikipedia)
// {¬, ∧}, {¬, ∨}, {¬, →}, {¬, ←}, {→, ⊥}, {←, ⊥}, {→, ⊕}, {←, ⊕},
// {→, ↚}, {←, ↚}, {→, ↛}, {←, ↛}, {¬, ↚}, {¬, ↛}, {⊤, ↚}, {⊤, ↛}, {↔, ↚}, {↔, ↛}

#[test]
fn two_op_not_and() {
    eprintln!("\n=== Testing {{NOT, AND}} ===");
    let depth = test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::AndAB2], 4);
    eprintln!("{{NOT, AND}}: All 16 functions found by depth {}\n", depth);
    assert_eq!(depth, 4);
}

#[test]
fn two_op_not_or() {
    eprintln!("\n=== Testing {{NOT, OR}} ===");
    let depth = test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::OrAB2], 4);
    eprintln!("{{NOT, OR}}: All 16 functions found by depth {}\n", depth);
    assert_eq!(depth, 4);
}

#[test]
fn two_op_not_implies() {
    eprintln!("\n=== Testing {{NOT, IMPLIES}} (¬, →) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::ImpliesAB2], 4);
    eprintln!(
        "{{NOT, IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_not_implied_by() {
    eprintln!("\n=== Testing {{NOT, IMPLIED-BY}} (¬, ←) ===");
    // A ← B is the same as B → A
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::ImpliesBA2], 4);
    eprintln!(
        "{{NOT, IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_implies_false() {
    eprintln!("\n=== Testing {{IMPLIES, FALSE}} (→, ⊥) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::ImpliesAB2, BooleanSimpleOp::False0], 4);
    eprintln!(
        "{{IMPLIES, FALSE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_implied_by_false() {
    eprintln!("\n=== Testing {{IMPLIED-BY, FALSE}} (←, ⊥) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::ImpliesBA2, BooleanSimpleOp::False0], 4);
    eprintln!(
        "{{IMPLIED-BY, FALSE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_implies_xor() {
    eprintln!("\n=== Testing {{IMPLIES, XOR}} (→, ⊕) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::ImpliesAB2, BooleanSimpleOp::XorAB2], 3);
    eprintln!(
        "{{IMPLIES, XOR}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 3);
}

#[test]
fn two_op_implied_by_xor() {
    eprintln!("\n=== Testing {{IMPLIED-BY, XOR}} (←, ⊕) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::ImpliesBA2, BooleanSimpleOp::XorAB2], 3);
    eprintln!(
        "{{IMPLIED-BY, XOR}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 3);
}

#[test]
fn two_op_implies_not_implied_by() {
    eprintln!("\n=== Testing {{IMPLIES, NOT-IMPLIED-BY}} (→, ↚) ===");
    // ↚ is NotImpliesBA2
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::ImpliesAB2, BooleanSimpleOp::NotImpliesBA2],
        2,
    );
    eprintln!(
        "{{IMPLIES, NOT-IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn two_op_implied_by_not_implied_by() {
    eprintln!("\n=== Testing {{IMPLIED-BY, NOT-IMPLIED-BY}} (←, ↚) ===");
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::ImpliesBA2, BooleanSimpleOp::NotImpliesBA2],
        2,
    );
    eprintln!(
        "{{IMPLIED-BY, NOT-IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn two_op_implies_not_implies() {
    eprintln!("\n=== Testing {{IMPLIES, NOT-IMPLIES}} (→, ↛) ===");
    // ↛ is NotImpliesAB2
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::ImpliesAB2, BooleanSimpleOp::NotImpliesAB2],
        2,
    );
    eprintln!(
        "{{IMPLIES, NOT-IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn two_op_implied_by_not_implies() {
    eprintln!("\n=== Testing {{IMPLIED-BY, NOT-IMPLIES}} (←, ↛) ===");
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::ImpliesBA2, BooleanSimpleOp::NotImpliesAB2],
        2,
    );
    eprintln!(
        "{{IMPLIED-BY, NOT-IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn two_op_not_not_implied_by() {
    eprintln!("\n=== Testing {{NOT, NOT-IMPLIED-BY}} (¬, ↚) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::NotImpliesBA2], 4);
    eprintln!(
        "{{NOT, NOT-IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_not_not_implies() {
    eprintln!("\n=== Testing {{NOT, NOT-IMPLIES}} (¬, ↛) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::NotA1, BooleanSimpleOp::NotImpliesAB2], 4);
    eprintln!(
        "{{NOT, NOT-IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_true_not_implied_by() {
    eprintln!("\n=== Testing {{TRUE, NOT-IMPLIED-BY}} (⊤, ↚) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::True0, BooleanSimpleOp::NotImpliesBA2], 4);
    eprintln!(
        "{{TRUE, NOT-IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_true_not_implies() {
    eprintln!("\n=== Testing {{TRUE, NOT-IMPLIES}} (⊤, ↛) ===");
    let depth =
        test_functional_completeness(&[BooleanSimpleOp::True0, BooleanSimpleOp::NotImpliesAB2], 4);
    eprintln!(
        "{{TRUE, NOT-IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 4);
}

#[test]
fn two_op_biimp_not_implied_by() {
    eprintln!("\n=== Testing {{BIIMP, NOT-IMPLIED-BY}} (↔, ↚) ===");
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::BiimpAB2, BooleanSimpleOp::NotImpliesBA2],
        3,
    );
    eprintln!(
        "{{BIIMP, NOT-IMPLIED-BY}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 3);
}

#[test]
fn two_op_biimp_not_implies() {
    eprintln!("\n=== Testing {{BIIMP, NOT-IMPLIES}} (↔, ↛) ===");
    let depth = test_functional_completeness(
        &[BooleanSimpleOp::BiimpAB2, BooleanSimpleOp::NotImpliesAB2],
        3,
    );
    eprintln!(
        "{{BIIMP, NOT-IMPLIES}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 3);
}

// Three-operator sets (6 from Wikipedia)
// {∨, ↔, ⊥}, {∨, ↔, ⊕}, {∨, ⊕, ⊤}, {∧, ↔, ⊥}, {∧, ↔, ⊕}, {∧, ⊕, ⊤}

#[test]
fn three_op_or_biimp_false() {
    eprintln!("\n=== Testing {{OR, BIIMP, FALSE}} (∨, ↔, ⊥) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::BiimpAB2,
            BooleanSimpleOp::False0,
        ],
        2,
    );
    eprintln!(
        "{{OR, BIIMP, FALSE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn three_op_or_biimp_xor() {
    eprintln!("\n=== Testing {{OR, BIIMP, XOR}} (∨, ↔, ⊕) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::BiimpAB2,
            BooleanSimpleOp::XorAB2,
        ],
        2,
    );
    eprintln!(
        "{{OR, BIIMP, XOR}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn three_op_or_xor_true() {
    eprintln!("\n=== Testing {{OR, XOR, TRUE}} (∨, ⊕, ⊤) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::XorAB2,
            BooleanSimpleOp::True0,
        ],
        2,
    );
    eprintln!(
        "{{OR, XOR, TRUE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn three_op_and_biimp_false() {
    eprintln!("\n=== Testing {{AND, BIIMP, FALSE}} (∧, ↔, ⊥) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::BiimpAB2,
            BooleanSimpleOp::False0,
        ],
        2,
    );
    eprintln!(
        "{{AND, BIIMP, FALSE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn three_op_and_biimp_xor() {
    eprintln!("\n=== Testing {{AND, BIIMP, XOR}} (∧, ↔, ⊕) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::BiimpAB2,
            BooleanSimpleOp::XorAB2,
        ],
        2,
    );
    eprintln!(
        "{{AND, BIIMP, XOR}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn three_op_and_xor_true() {
    eprintln!("\n=== Testing {{AND, XOR, TRUE}} (∧, ⊕, ⊤) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::XorAB2,
            BooleanSimpleOp::True0,
        ],
        2,
    );
    eprintln!(
        "{{AND, XOR, TRUE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn four_op_and_or_xor_true() {
    eprintln!("\n=== Testing {{AND, OR, XOR, TRUE}} (∧, ∨, ⊕, ⊤) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::XorAB2,
            BooleanSimpleOp::True0,
        ],
        2,
    );
    eprintln!(
        "{{AND, OR, XOR, TRUE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn four_op_not_and_or_xor() {
    eprintln!("\n=== Testing {{NOT, AND, OR, XOR}} (¬, ∧, ∨, ⊕) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::NotA1,
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::XorAB2,
        ],
        2,
    );
    eprintln!(
        "{{NOT, AND, OR, XOR}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}

#[test]
fn five_op_not_and_or_xor_true() {
    eprintln!("\n=== Testing {{NOT, AND, OR, XOR, TRUE}} (¬, ∧, ∨, ⊕, ⊤) ===");
    let depth = test_functional_completeness(
        &[
            BooleanSimpleOp::NotA1,
            BooleanSimpleOp::AndAB2,
            BooleanSimpleOp::OrAB2,
            BooleanSimpleOp::XorAB2,
            BooleanSimpleOp::True0,
        ],
        2,
    );
    eprintln!(
        "{{NOT, AND, OR, XOR, TRUE}}: All 16 functions found by depth {}\n",
        depth
    );
    assert_eq!(depth, 2);
}
