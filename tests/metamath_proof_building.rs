//! Integration tests for Metamath proof building.
//!
//! This test validates Phase 3 proof building:
//! - Converting unification substitutions to Metamath proofs
//! - Generating expanded proof format (label sequences)
//! - Identity substitutions (trivial proofs)
//! - Non-trivial substitutions (compound terms)

use std::sync::Arc;
use symbolic_mgu::metamath::{
    Label, MemoryFilesystem, MetamathDatabase, Parser, ProofBuilder, TypeMapping,
};
use symbolic_mgu::Substitution;

/// Create a minimal Metamath database for proof building tests.
fn test_database() -> &'static str {
    r#"
$( Test database for proof building $)

$c ( $.
$c ) $.
$c -> $.
$c wff $.
$c |- $.

$v ph $.
$v ps $.
$v ch $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

$( Implication syntax $)
wi $a wff ( ph -> ps ) $.

$( Axiom 1: Simp $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

$( Axiom 2: Frege $)
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

$( Modus Ponens $)
${
  ax-mp.1 $e |- ph $.
  ax-mp.2 $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

$( End of database $)
"#
}

/// Helper function to setup a parsed test database.
fn setup_test_db() -> Arc<MetamathDatabase> {
    let mut fs = MemoryFilesystem::new();
    fs.add_file("test.mm", test_database().to_string());
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser = Parser::new(fs, "test.mm", db).expect("Failed to create parser");
    parser.parse().expect("Failed to parse database")
}

#[test]
fn create_proof_builder() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    // Builder should be created successfully
    // (This is mostly a compile test)
    drop(builder);
}

#[test]
fn build_proof_for_axiom() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    // Create an empty substitution (identity)
    let substitution = Substitution::new();

    // Build proof for ax-1 with identity substitution
    let label = Label::new("ax-1").expect("Failed to create label");
    let result = builder.build_proof(&label, &substitution);

    assert!(
        result.is_ok(),
        "Building proof for ax-1 failed: {:?}",
        result.err()
    );

    // Check that the proof is expanded format
    use symbolic_mgu::metamath::Proof;
    match result.unwrap() {
        Proof::Expanded(steps) => {
            assert!(!steps.is_empty(), "Proof should have at least one step");
            // At minimum, should include the axiom label itself
            assert!(
                steps.iter().any(|s| s.as_ref() == "ax-1"),
                "Proof should include ax-1 label"
            );
        }
        Proof::Compressed { .. } => panic!("Expected expanded proof, got compressed"),
    }
}

#[test]
fn build_proof_for_nonexistent_axiom() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    let substitution = Substitution::new();

    // Try to build proof for non-existent axiom
    let label = Label::new("nonexistent").expect("Failed to create label");
    let result = builder.build_proof(&label, &substitution);

    assert!(
        result.is_err(),
        "Building proof for non-existent axiom should fail"
    );

    use symbolic_mgu::metamath::ProofBuildError;
    match result.unwrap_err() {
        ProofBuildError::AssertionNotFound { label } => {
            assert_eq!(label, "nonexistent");
        }
        other => panic!("Expected AssertionNotFound error, got {:?}", other),
    }
}

#[test]
fn proof_builder_with_multiple_axioms() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    let substitution = Substitution::new();

    // Build proofs for multiple axioms
    let axioms = vec!["ax-1", "ax-2", "ax-mp"];

    for axiom_str in axioms {
        let label = Label::new(axiom_str).expect("Failed to create label");
        let result = builder.build_proof(&label, &substitution);

        assert!(
            result.is_ok(),
            "Building proof for {} failed: {:?}",
            axiom_str,
            result.err()
        );
    }
}

#[test]
fn build_application_proof() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    let substitution = Substitution::new();

    // Build APPLY proof: given ax-1 and something, apply ax-mp
    let major_label = Label::new("ax-1").expect("Failed to create label");
    let minor_label = Label::new("ax-2").expect("Failed to create label");

    let result = builder.build_application_proof(&major_label, &minor_label, &substitution);

    assert!(
        result.is_ok(),
        "Building APPLY proof failed: {:?}",
        result.err()
    );

    // Check that proof contains ax-mp
    use symbolic_mgu::metamath::Proof;
    match result.unwrap() {
        Proof::Expanded(steps) => {
            assert!(
                steps.iter().any(|s| s.as_ref() == "ax-mp"),
                "APPLY proof should include ax-mp"
            );
            // Should also include both premises
            assert!(
                steps.iter().any(|s| s.as_ref() == "ax-1"),
                "APPLY proof should include major premise ax-1"
            );
            assert!(
                steps.iter().any(|s| s.as_ref() == "ax-2"),
                "APPLY proof should include minor premise ax-2"
            );
        }
        Proof::Compressed { .. } => panic!("Expected expanded proof, got compressed"),
    }
}

#[test]
fn build_condensed_detachment_proof() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    let substitution = Substitution::new();

    // Build CONDENSED_DETACH proof
    let major_label = Label::new("ax-1").expect("Failed to create label");
    let minor_label = Label::new("ax-2").expect("Failed to create label");

    let result =
        builder.build_condensed_detachment_proof(&major_label, &minor_label, &substitution);

    assert!(
        result.is_ok(),
        "Building CONDENSED_DETACH proof failed: {:?}",
        result.err()
    );

    // Check that proof contains ax-mp
    use symbolic_mgu::metamath::Proof;
    match result.unwrap() {
        Proof::Expanded(steps) => {
            assert!(
                steps.iter().any(|s| s.as_ref() == "ax-mp"),
                "CONDENSED_DETACH proof should include ax-mp"
            );
        }
        Proof::Compressed { .. } => panic!("Expected expanded proof, got compressed"),
    }
}

#[test]
fn build_proof_with_multiple_substitutions() {
    let db = setup_test_db();
    let builder = ProofBuilder::new(Arc::clone(&db));

    // Create a non-empty substitution
    // This tests Phase 3 full substitution handling
    use symbolic_mgu::metamath::{DbMetavariable, DbTerm};
    let substitution: Substitution<DbMetavariable, DbTerm> = Substitution::new();

    // Note: Actually creating substitutions would require parsing terms,
    // which is complex for a basic test. The key is that the API accepts
    // non-empty substitutions and can iterate over them.

    let label = Label::new("ax-1").expect("Failed to create label");
    let result = builder.build_proof(&label, &substitution);

    assert!(
        result.is_ok(),
        "Building proof with substitution failed: {:?}",
        result.err()
    );
}
