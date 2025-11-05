//! Regression tests for compact proof parsing.
//!
//! These tests validate bug fixes discovered during rustmgu development.

use symbolic_mgu::{
    logic::create_dict, test_tautology, EnumTermFactory, MetaByteFactory, MguError, NodeByte,
    Statement, TermFactory,
};

/// Helper to parse a compact proof and verify it produces a valid statement
fn parse_compact_proof(proof: &str) -> Result<bool, MguError> {
    let var_factory = MetaByteFactory();
    let term_factory = EnumTermFactory::new();

    let dict = create_dict(&term_factory, &var_factory, NodeByte::Implies, NodeByte::Not)?;

    let result = Statement::from_compact_proof(proof, &var_factory, &term_factory, &dict)?;

    // For theorems (no hypotheses), verify the assertion is a tautology
    if result.get_n_hypotheses() == 0 {
        test_tautology(result.get_assertion())
    } else {
        // For inferences with hypotheses, build H₁ → (H₂ → (... → A))
        let mut implication = result.get_assertion().clone();

        for hyp in result.get_hypotheses().iter().rev() {
            implication =
                term_factory.create_node(NodeByte::Implies, vec![hyp.clone(), implication])?;
        }

        test_tautology(&implication)
    }
}

/// Regression test for DDD111D23
///
/// This proof exposed a bug in rustmgu where statements were not made disjoint
/// before unification in apply/apply_multiple operations.
///
/// Expected output (Polish notation): >P>>>~Q~RR>>~Q~RQ
/// Where > is Implies, ~ is Not
///
/// TODO: Verify exact canonical form once statement equivalence is implemented.
#[test]
fn regression_ddd111d23_produces_tautology() {
    let proof = "DDD111D23";

    match parse_compact_proof(proof) {
        Ok(true) => {
            // Success: parsed and verified as tautology
        }
        Ok(false) => {
            panic!("Proof {} parsed but did NOT produce a tautology", proof);
        }
        Err(e) => {
            panic!("Proof {} failed to parse: {}", proof, e);
        }
    }
}

/// Regression test for DDD1D221D2D2D11
///
/// This proof also exposed the disjointness bug in rustmgu.
///
/// Expected output (Polish notation): >>>>>PQRQ>>PQR>>>>PQRQR
/// Where > is Implies
///
/// TODO: Verify exact canonical form once statement equivalence is implemented.
#[test]
fn regression_ddd1d221d2d2d11_produces_tautology() {
    let proof = "DDD1D221D2D2D11";

    match parse_compact_proof(proof) {
        Ok(true) => {
            // Success: parsed and verified as tautology
        }
        Ok(false) => {
            panic!("Proof {} parsed but did NOT produce a tautology", proof);
        }
        Err(e) => {
            panic!("Proof {} failed to parse: {}", proof, e);
        }
    }
}

/// Test both proofs parse without errors (validates disjointness fix)
#[test]
fn regression_proofs_parse_successfully() {
    let var_factory = MetaByteFactory();
    let term_factory = EnumTermFactory::new();
    let dict = create_dict(&term_factory, &var_factory, NodeByte::Implies, NodeByte::Not)
        .expect("Failed to create dictionary");

    // DDD111D23 should parse
    let result1 = Statement::from_compact_proof("DDD111D23", &var_factory, &term_factory, &dict);
    assert!(
        result1.is_ok(),
        "DDD111D23 failed to parse: {}",
        result1.unwrap_err()
    );

    // DDD1D221D2D2D11 should parse
    let result2 =
        Statement::from_compact_proof("DDD1D221D2D2D11", &var_factory, &term_factory, &dict);
    assert!(
        result2.is_ok(),
        "DDD1D221D2D2D11 failed to parse: {}",
        result2.unwrap_err()
    );
}

/// Verify the disjointness bug is actually fixed by checking that
/// relabel_disjoint is being called before unification.
///
/// The bug was: apply() and apply_multiple() were unifying statements
/// without first ensuring their variables were disjoint, causing
/// occurs-check failures and incorrect results.
#[test]
fn disjointness_is_enforced_in_apply() {
    let var_factory = MetaByteFactory();
    let term_factory = EnumTermFactory::new();

    let dict = create_dict(&term_factory, &var_factory, NodeByte::Implies, NodeByte::Not)
        .expect("Failed to create dictionary");

    // Get Modus Ponens (has 2 hypotheses) and Simp (axiom)
    let modus_ponens = dict.get("D").expect("Modus Ponens not in dict").clone();
    let simp = dict.get("1").expect("Simp not in dict").clone();

    // Apply Simp to MP's first hypothesis
    // Without proper disjointness handling, this could fail or produce incorrect results
    let result = modus_ponens.apply(&var_factory, &term_factory, 0, &simp);

    assert!(
        result.is_ok(),
        "Apply failed (disjointness bug?): {}",
        result.unwrap_err()
    );

    // The result should be a valid statement
    let statement = result.unwrap();
    assert!(
        statement.get_n_hypotheses() >= 1,
        "Expected at least one hypothesis after apply"
    );
}
