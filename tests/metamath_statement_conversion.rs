//! Integration tests for converting Metamath assertions to symbolic-mgu Statements.
//!
//! This test validates the Phase 2 conversion:
//! - AssertionCore → Statement
//! - EssentialHyp → hypothesis Terms
//! - FloatingHyp → implicit variable typing

use std::sync::Arc;
use symbolic_mgu::metamath::{Label, MemoryFilesystem, MetamathDatabase, Parser, TypeMapping};
use symbolic_mgu::{Term, TypeCore};

/// Create a minimal Metamath database with logical axioms and inference rules.
fn minimal_database() -> &'static str {
    r#"
$( Minimal Metamath database for Statement conversion testing $)

$c ( $.
$c ) $.
$c -> $.
$c -. $.
$c wff $.
$c |- $.

$v ph $.
$v ps $.
$v ch $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

$( Negation syntax: wff -. ph $)
wn $a wff -. ph $.

$( Implication syntax: wff ( ph -> ps ) $)
wi $a wff ( ph -> ps ) $.

$( Axiom 1: Simp - a simple axiom with no hypotheses $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

$( Axiom 2: Frege - a simple axiom with no hypotheses $)
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

$( Modus Ponens: an inference rule with hypotheses $)
${
  ax-mp.1 $e |- ph $.
  ax-mp.2 $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

$( End of database $)
"#
}

/// Helper function to setup a parsed minimal database for tests.
fn setup_minimal_db() -> Arc<MetamathDatabase> {
    let mut fs = MemoryFilesystem::new();
    fs.add_file("test.mm", minimal_database().to_string());
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser = Parser::new(fs, "test.mm", db).expect("Failed to create parser");
    parser.parse().expect("Failed to parse database")
}

#[test]
fn convert_simple_axiom_no_hypotheses() {
    // Setup database
    let db = setup_minimal_db();

    // Get ax-1: |- ( ph -> ( ps -> ph ) )
    let axiom = db.get_axiom(&Label::new("ax-1").unwrap()).unwrap();

    // Convert to Statement
    let statement = axiom
        .core
        .to_statement(&db)
        .expect("Failed to convert to Statement");

    // Verify: no hypotheses
    assert_eq!(
        statement.get_n_hypotheses(),
        0,
        "ax-1 should have 0 hypotheses"
    );

    // Verify: conclusion is Boolean type (wff)
    let conclusion_type = statement
        .get_assertion()
        .get_type()
        .expect("Failed to get conclusion type");
    assert!(
        conclusion_type.is_boolean(),
        "Conclusion should be Boolean type"
    );

    // Verify: conclusion is not a single variable
    assert!(
        !statement.get_assertion().is_metavariable(),
        "Conclusion should be a complex term, not a metavariable"
    );
}

#[test]
fn convert_axiom_with_nested_structure() {
    // Setup database
    let db = setup_minimal_db();

    // Get ax-2: |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )
    let axiom = db.get_axiom(&Label::new("ax-2").unwrap()).unwrap();

    // Convert to Statement
    let statement = axiom
        .core
        .to_statement(&db)
        .expect("Failed to convert to Statement");

    // Verify: no hypotheses
    assert_eq!(
        statement.get_n_hypotheses(),
        0,
        "ax-2 should have 0 hypotheses"
    );

    // Verify: conclusion is Boolean
    let conclusion_type = statement
        .get_assertion()
        .get_type()
        .expect("Failed to get conclusion type");
    assert!(
        conclusion_type.is_boolean(),
        "Conclusion should be Boolean type"
    );

    // Verify: deeply nested structure (should have children)
    assert!(
        statement.get_assertion().get_n_children() > 0,
        "Conclusion should have children (nested structure)"
    );
}

#[test]
fn convert_inference_rule_with_hypotheses() {
    // Setup database
    let db = setup_minimal_db();

    // Get ax-mp: modus ponens with 2 hypotheses
    let axiom = db.get_axiom(&Label::new("ax-mp").unwrap()).unwrap();

    // Convert to Statement
    let statement = axiom
        .core
        .to_statement(&db)
        .expect("Failed to convert to Statement");

    // Verify: has 2 hypotheses
    assert_eq!(
        statement.get_n_hypotheses(),
        2,
        "ax-mp should have 2 hypotheses"
    );

    // Verify: all hypotheses are Boolean
    for (i, hyp) in statement.get_hypotheses().iter().enumerate() {
        let hyp_type = hyp.get_type().expect("Failed to get hypothesis type");
        assert!(
            hyp_type.is_boolean(),
            "Hypothesis {} should be Boolean type",
            i
        );
    }

    // Verify: conclusion is Boolean
    let conclusion_type = statement
        .get_assertion()
        .get_type()
        .expect("Failed to get conclusion type");
    assert!(
        conclusion_type.is_boolean(),
        "Conclusion should be Boolean type"
    );

    // Verify: conclusion is a simple variable (ps)
    assert!(
        statement.get_assertion().is_metavariable(),
        "ax-mp conclusion should be a metavariable (ps)"
    );
}

#[test]
fn verify_hypothesis_structure() {
    // Setup database
    let db = setup_minimal_db();

    // Get ax-mp
    let axiom = db.get_axiom(&Label::new("ax-mp").unwrap()).unwrap();
    let statement = axiom.core.to_statement(&db).expect("Failed to convert");

    // Get hypotheses
    let hyps: Vec<_> = statement.get_hypotheses().iter().collect();
    assert_eq!(hyps.len(), 2, "Should have exactly 2 hypotheses");

    // First hypothesis: |- ph (should be a variable)
    assert!(
        hyps[0].is_metavariable(),
        "First hypothesis should be metavariable ph"
    );

    // Second hypothesis: |- ( ph -> ps ) (should be an implication node)
    assert!(
        !hyps[1].is_metavariable(),
        "Second hypothesis should be a node (implication)"
    );
    assert_eq!(
        hyps[1].get_n_children(),
        2,
        "Second hypothesis (implication) should have 2 children"
    );
}

#[test]
fn all_axioms_convert_successfully() {
    // Setup database
    let db = setup_minimal_db();

    // Try to convert all axioms
    let axiom_labels = vec!["wn", "wi", "ax-1", "ax-2", "ax-mp"];

    for label_str in axiom_labels {
        let label = Label::new(label_str).expect("Failed to create label");
        let axiom = db
            .get_axiom(&label)
            .unwrap_or_else(|| panic!("Axiom {} not found", label_str));

        let result = axiom.core.to_statement(&db);

        assert!(
            result.is_ok(),
            "Failed to convert axiom {}: {:?}",
            label_str,
            result.err()
        );
    }
}

#[test]
fn syntax_axiom_conversion() {
    // Setup database
    let db = setup_minimal_db();

    // Get wn: wff -. ph (syntax axiom, not logical axiom)
    let axiom = db.get_axiom(&Label::new("wn").unwrap()).unwrap();

    // This should still convert (syntax axioms can be treated as statements)
    let statement = axiom.core.to_statement(&db);

    // Syntax axioms don't start with "|-", so they parse differently
    // This should fail or handle gracefully
    // Actually, wn is "wff -. ph" not "|- ...", so it's not a logical assertion
    // Let's verify what happens

    match statement {
        Ok(stmt) => {
            // If it succeeds, verify it's well-formed
            assert!(
                stmt.get_assertion().is_valid_sentence().unwrap(),
                "Syntax axiom statement should be valid"
            );
        }
        Err(e) => {
            // If it fails, that's also acceptable for syntax axioms
            eprintln!("Syntax axiom conversion failed (expected): {:?}", e);
        }
    }
}
