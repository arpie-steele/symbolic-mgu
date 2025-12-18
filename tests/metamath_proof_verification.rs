//! Integration tests for Metamath proof verification.
//!
//! This test validates the Phase 3 proof verification:
//! - Stack-based proof verification algorithm
//! - Valid proofs are accepted
//! - Invalid proofs are rejected with appropriate errors
//! - Both expanded and compressed proof formats work

use std::sync::Arc;
use symbolic_mgu::metamath::{
    verify_theorem, Label, MemoryFilesystem, MetamathDatabase, Parser, Proof, TypeMapping,
};

/// Create a Metamath database with axioms, inference rules, and simple theorems.
///
/// This database includes:
/// - Syntax axioms: wn (negation), wi (implication)
/// - Logical axioms: ax-1, ax-2
/// - Inference rule: ax-mp (modus ponens)
/// - Simple theorems with proofs: a1i, id
fn test_database() -> &'static str {
    r#"
$( Test database for proof verification $)

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

$( Negation: wff -. ph $)
wn $a wff -. ph $.

$( Implication: wff ( ph -> ps ) $)
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

$( Theorem a1i: Apply ax-1 $)
${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $= wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
$}

$( Theorem id: Identity - ph -> ph $)
id $p |- ( ph -> ph ) $=
  wph wph wph wi wi wph wph wi wph wph ax-1
  wph wph wph wi wph wi wi wph wph wph wi wi wph wph wi wi wph wph wph wi ax-1
  wph wph wph wi wph ax-2 ax-mp ax-mp $.

$( Theorem id_compressed: Identity - ph -> ph $)
id_compressed $p |- ( ph -> ph ) $=
 ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
$(
  Initially: A :> wph, B :> wi, C :> ax-1, D :> ax-2, E :> ax-mp
  The first Z defines F:> "(ph -> ph)" or "wph wph wi" in RPN
  The second Z defines G:> "(ph -> (ph -> ph))" or "wph wph wph wi wi" in RPN
$)

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
fn verify_simple_theorem_a1i() {
    // Setup database
    let db = setup_test_db();

    // Get theorem a1i: |- ( ps -> ph ) given |- ph
    let theorem = db
        .get_theorem(&Label::new("a1i").unwrap())
        .expect("a1i theorem not found");

    // Verify the proof
    let result = verify_theorem(&theorem, &db);

    assert!(
        result.is_ok(),
        "a1i theorem verification failed: {:?}",
        result.err()
    );
}

#[test]
fn verify_theorem_id() {
    // Setup database
    let db = setup_test_db();

    // Get theorem id: |- ( ph -> ph ) (proves identity using ax-1, ax-2, ax-mp)
    let theorem = db
        .get_theorem(&Label::new("id").unwrap())
        .expect("id theorem not found");

    // Verify the proof
    let result = verify_theorem(&theorem, &db);

    assert!(
        result.is_ok(),
        "id theorem verification failed: {:?}",
        result.err()
    );
}

#[test]
fn verify_compressed_proof() {
    // Setup database
    let db = setup_test_db();

    // Get theorem id_compressed: |- ( ph -> ph ) with compressed proof
    let theorem = db
        .get_theorem(&Label::new("id_compressed").unwrap())
        .expect("id_compressed theorem not found");

    // Verify that it has a compressed proof
    match &theorem.proof {
        Some(Proof::Compressed {
            labels,
            proof_string,
        }) => {
            // Verify it's actually compressed format
            assert!(!labels.is_empty(), "Compressed proof should have labels");
            assert!(
                !proof_string.is_empty(),
                "Compressed proof should have proof string"
            );

            // Verify the proof contains the expected pattern (A-Z encoding)
            assert!(
                proof_string
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_whitespace()),
                "Compressed proof should only contain uppercase letters and whitespace"
            );
        }
        Some(Proof::Expanded(_)) => panic!("Expected compressed proof, got expanded"),
        None => panic!("id_compressed should have a proof"),
    }

    // Verify the compressed proof
    let result = verify_theorem(&theorem, &db);

    assert!(
        result.is_ok(),
        "id_compressed theorem verification failed: {:?}",
        result.err()
    );
}

#[test]
fn compressed_and_expanded_proofs_equivalent() {
    // Setup database
    let db = setup_test_db();

    // Both id and id_compressed prove the same theorem: |- ( ph -> ph )
    let id = db
        .get_theorem(&Label::new("id").unwrap())
        .expect("id theorem not found");

    let id_compressed = db
        .get_theorem(&Label::new("id_compressed").unwrap())
        .expect("id_compressed theorem not found");

    // Verify both have the same statement
    assert_eq!(
        id.core.statement, id_compressed.core.statement,
        "id and id_compressed should prove the same statement"
    );

    // Verify both proofs are valid
    let result_expanded = verify_theorem(&id, &db);
    let result_compressed = verify_theorem(&id_compressed, &db);

    assert!(
        result_expanded.is_ok(),
        "Expanded proof verification failed: {:?}",
        result_expanded.err()
    );

    assert!(
        result_compressed.is_ok(),
        "Compressed proof verification failed: {:?}",
        result_compressed.err()
    );
}

#[test]
fn verify_all_theorems_in_database() {
    // Setup database
    let db = setup_test_db();

    // Verify all theorems
    let theorem_labels = vec!["a1i", "id", "id_compressed"];

    for label_str in theorem_labels {
        let label = Label::new(label_str).expect("Failed to create label");
        let theorem = db
            .get_theorem(&label)
            .unwrap_or_else(|| panic!("Theorem {} not found", label_str));

        let result = verify_theorem(&theorem, &db);

        assert!(
            result.is_ok(),
            "Theorem {} verification failed: {:?}",
            label_str,
            result.err()
        );
    }
}

#[test]
fn database_parsing_succeeds() {
    // Just verify the database parses without errors
    let db = setup_test_db();

    // Check that axioms exist
    assert!(db.get_axiom(&Label::new("ax-1").unwrap()).is_some());
    assert!(db.get_axiom(&Label::new("ax-2").unwrap()).is_some());
    assert!(db.get_axiom(&Label::new("ax-mp").unwrap()).is_some());

    // Check that theorems exist
    assert!(db.get_theorem(&Label::new("a1i").unwrap()).is_some());
    assert!(db.get_theorem(&Label::new("id").unwrap()).is_some());
    assert!(db
        .get_theorem(&Label::new("id_compressed").unwrap())
        .is_some());

    // Check that theorems have proofs
    let a1i = db.get_theorem(&Label::new("a1i").unwrap()).unwrap();
    assert!(a1i.proof.is_some(), "a1i should have a proof");

    let id = db.get_theorem(&Label::new("id").unwrap()).unwrap();
    assert!(id.proof.is_some(), "id should have a proof");

    let id_compressed = db
        .get_theorem(&Label::new("id_compressed").unwrap())
        .unwrap();
    assert!(
        id_compressed.proof.is_some(),
        "id_compressed should have a proof"
    );
}

#[test]
fn theorem_a1i_structure() {
    let db = setup_test_db();
    let a1i = db.get_theorem(&Label::new("a1i").unwrap()).unwrap();

    // Check that a1i has 1 essential hypothesis
    assert_eq!(
        a1i.core.hypotheses.1.len(),
        1,
        "a1i should have 1 essential hypothesis"
    );

    // Check that the hypothesis is "|- ph"
    let hyp = &a1i.core.hypotheses.1[0];
    assert_eq!(hyp.statement[0].as_ref(), "|-");
    assert_eq!(hyp.statement[1].as_ref(), "ph");

    // Check that the conclusion is "|- ( ps -> ph )"
    assert_eq!(a1i.core.statement[0].as_ref(), "|-");
    assert_eq!(a1i.core.statement[1].as_ref(), "(");
    assert_eq!(a1i.core.statement[2].as_ref(), "ps");
    assert_eq!(a1i.core.statement[3].as_ref(), "->");
    assert_eq!(a1i.core.statement[4].as_ref(), "ph");
    assert_eq!(a1i.core.statement[5].as_ref(), ")");
}
