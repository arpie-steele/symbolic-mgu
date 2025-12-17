//! Integration test for Metamath expression parsing.
//!
//! This test validates the end-to-end flow:
//! 1. Parse a minimal Metamath database (propositional logic basics)
//! 2. Verify symbol registration works correctly
//! 3. Verify syntax axiom indexing works correctly
//! 4. Test parse_expression() on real Metamath expressions

use std::sync::Arc;
use symbolic_mgu::metamath::{parse_expression, MetamathDatabase, Parser, TypeMapping};
use symbolic_mgu::Term;

/// Create a minimal Metamath database string with propositional logic basics.
///
/// This includes:
/// - Constants: (, ), ->, -., wff, |-
/// - Variables: ph, ps
/// - Floating hypotheses: wph, wps
/// - Syntax axioms: wn (negation), wi (implication)
/// - Logical axiom: ax-1
fn minimal_database() -> &'static str {
    r#"
$( Minimal Metamath database for testing expression parsing $)

$c ( $.
$c ) $.
$c -> $.
$c -. $.
$c wff $.
$c |- $.

$v ph $.
$v ps $.

wph $f wff ph $.
wps $f wff ps $.

$( Negation: wff -. ph $)
wn $a wff -. ph $.

$( Implication: wff ( ph -> ps ) $)
wi $a wff ( ph -> ps ) $.

$( Axiom 1: Simp $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

$( End of database $)
"#
}

/// Helper function to setup a parsed minimal database for tests.
fn setup_minimal_db() -> Arc<MetamathDatabase> {
    let mut fs = symbolic_mgu::metamath::MemoryFilesystem::new();
    fs.add_file("test.mm", minimal_database().to_string());
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser = Parser::new(fs, "test.mm", db).expect("Failed to create parser");
    parser.parse().expect("Failed to parse database")
}

#[test]
fn parse_minimal_database() {
    // Setup database
    let db = setup_minimal_db();

    // Verify constants are registered
    assert!(db.is_constant("("), "( should be registered as constant");
    assert!(db.is_constant(")"), ") should be registered as constant");
    assert!(db.is_constant("->"), "-> should be registered as constant");
    assert!(db.is_constant("-."), "-. should be registered as constant");
    assert!(
        db.is_constant("wff"),
        "wff should be registered as constant"
    );
    assert!(db.is_constant("|-"), "|- should be registered as constant");

    // Verify variables are registered
    assert!(
        db.is_variable_symbol("ph"),
        "ph should be registered as variable"
    );
    assert!(
        db.is_variable_symbol("ps"),
        "ps should be registered as variable"
    );

    // Constants should not be variables and vice versa
    assert!(!db.is_variable_symbol("("), "( should not be a variable");
    assert!(!db.is_constant("ph"), "ph should not be a constant");

    // Verify floating hypotheses exist
    let float_ph = db.lookup_floating_hyp("wff", "ph");
    assert!(float_ph.is_some(), "wph floating hypothesis should exist");

    let float_ps = db.lookup_floating_hyp("wff", "ps");
    assert!(float_ps.is_some(), "wps floating hypothesis should exist");

    // Verify syntax axioms are indexed
    let wff_axioms = db.get_syntax_axioms_for_type("wff");
    assert!(
        !wff_axioms.is_empty(),
        "Should have syntax axioms for wff type"
    );
    assert_eq!(
        wff_axioms.len(),
        2,
        "Should have exactly 2 syntax axioms (wn and wi)"
    );

    // Check that wn and wi are indexed
    let labels: Vec<String> = wff_axioms
        .iter()
        .map(|p| p.label.as_str().to_string())
        .collect();
    assert!(labels.contains(&"wn".to_string()), "wn should be indexed");
    assert!(labels.contains(&"wi".to_string()), "wi should be indexed");
}

#[test]
fn parse_simple_variable() {
    // Setup database
    let db = setup_minimal_db();

    // Parse a simple variable: [wff, ph]
    let symbols = vec![Arc::from("wff"), Arc::from("ph")];
    let term = parse_expression(&symbols, &db).expect("Failed to parse variable");

    // Should be a metavariable
    assert!(term.is_metavariable(), "Should parse as metavariable");
}

#[test]
fn parse_negation() {
    // Setup database
    let db = setup_minimal_db();

    // Parse negation: [wff, -., ph]
    let symbols = vec![Arc::from("wff"), Arc::from("-."), Arc::from("ph")];
    let term = parse_expression(&symbols, &db).expect("Failed to parse negation");

    // Should be a node (not a metavariable)
    assert!(
        !term.is_metavariable(),
        "Negation should be a node, not metavariable"
    );

    // Should have 1 child (unary operator)
    assert_eq!(
        term.get_n_children(),
        1,
        "Negation should have exactly 1 child"
    );
}

#[test]
fn parse_implication() {
    // Setup database
    let db = setup_minimal_db();

    // Parse implication: [wff, (, ph, ->, ps, )]
    let symbols = vec![
        Arc::from("wff"),
        Arc::from("("),
        Arc::from("ph"),
        Arc::from("->"),
        Arc::from("ps"),
        Arc::from(")"),
    ];
    let term = parse_expression(&symbols, &db).expect("Failed to parse implication");

    // Should be a node
    assert!(
        !term.is_metavariable(),
        "Implication should be a node, not metavariable"
    );

    // Should have 2 children (binary operator)
    assert_eq!(
        term.get_n_children(),
        2,
        "Implication should have exactly 2 children"
    );
}

#[test]
fn parse_nested_implication() {
    // Setup database
    let db = setup_minimal_db();

    // Parse nested: [wff, (, ph, ->, (, ps, ->, ph, ), )]
    // This is the statement of ax-1: ph -> (ps -> ph)
    let symbols = vec![
        Arc::from("wff"),
        Arc::from("("),
        Arc::from("ph"),
        Arc::from("->"),
        Arc::from("("),
        Arc::from("ps"),
        Arc::from("->"),
        Arc::from("ph"),
        Arc::from(")"),
        Arc::from(")"),
    ];
    let term = parse_expression(&symbols, &db).expect("Failed to parse nested implication");

    // Should be a node
    assert!(
        !term.is_metavariable(),
        "Nested implication should be a node"
    );

    // Should have 2 children
    assert_eq!(
        term.get_n_children(),
        2,
        "Top-level implication should have 2 children"
    );

    // The second child should also be an implication (not a variable)
    let children: Vec<_> = term.get_children().collect();
    let second_child = &children[1];
    assert!(
        !second_child.is_metavariable(),
        "Second child should be a node (nested implication)"
    );
    assert_eq!(
        second_child.get_n_children(),
        2,
        "Nested implication should have 2 children"
    );
}

#[test]
fn parse_negated_implication() {
    // Setup database
    let db = setup_minimal_db();

    // Parse: [wff, -., (, ph, ->, ps, )]
    // This is: -.(ph -> ps)
    let symbols = vec![
        Arc::from("wff"),
        Arc::from("-."),
        Arc::from("("),
        Arc::from("ph"),
        Arc::from("->"),
        Arc::from("ps"),
        Arc::from(")"),
    ];
    let term = parse_expression(&symbols, &db).expect("Failed to parse negated implication");

    // Should be a node (negation)
    assert!(!term.is_metavariable(), "Should be a node");

    // Should have 1 child (negation is unary)
    assert_eq!(term.get_n_children(), 1, "Negation should have 1 child");

    // The child should be an implication
    let children: Vec<_> = term.get_children().collect();
    let child = &children[0];
    assert!(!child.is_metavariable(), "Child should be a node");
    assert_eq!(
        child.get_n_children(),
        2,
        "Child (implication) should have 2 children"
    );
}

#[test]
fn parse_error_unknown_symbol() {
    // Setup database
    let db = setup_minimal_db();

    // Try to parse unknown variable: [wff, unknown]
    let symbols = vec![Arc::from("wff"), Arc::from("unknown")];
    let result = parse_expression(&symbols, &db);

    assert!(result.is_err(), "Should fail on unknown symbol");
}

#[test]
fn parse_error_empty_sequence() {
    // Setup database
    let db = setup_minimal_db();

    // Try to parse empty sequence
    let symbols = vec![];
    let result = parse_expression(&symbols, &db);

    assert!(result.is_err(), "Should fail on empty sequence");
}

#[test]
fn parse_error_malformed_expression() {
    // Setup database
    let db = setup_minimal_db();

    // Try to parse malformed: [wff, (, ph]
    // Missing -> ps )
    let symbols = vec![Arc::from("wff"), Arc::from("("), Arc::from("ph")];
    let result = parse_expression(&symbols, &db);

    assert!(
        result.is_err(),
        "Should fail on malformed expression (missing closing paren and operator)"
    );
}

#[test]
fn debug_pattern_registration() {
    // Setup database
    let db = setup_minimal_db();

    // Check what syntax axioms are registered
    let wff_axioms = db.get_syntax_axioms_for_type("wff");
    eprintln!("Found {} syntax axioms for wff:", wff_axioms.len());

    for axiom in &wff_axioms {
        eprintln!("  Label: {}", axiom.label.as_str());
        eprintln!("  Pattern: {:?}", axiom.pattern);
        eprintln!("  Hints:");
        eprintln!("    first_constant: {:?}", axiom.hints.first_constant);
        eprintln!("    last_constant: {:?}", axiom.hints.last_constant);
        eprintln!(
            "    constants_in_order: {:?}",
            axiom.hints.constants_in_order
        );
        eprintln!("    arity: {}", axiom.hints.arity);
        eprintln!();
    }
}
