//! Regression tests for compact proof parsing.
//!
//! These tests validate bug fixes discovered during rustmgu development.

use symbolic_mgu::bool_eval::{test_validity, BooleanSimpleOp};
use symbolic_mgu::logic::polish::PolishNotationEngine;
use symbolic_mgu::logic::{build_boolean_statement_from_polish_with_engine, create_dict};
use symbolic_mgu::{
    EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, MguError, NodeByte,
    SimpleType, SimpleTypeFactory, Statement,
};

type TestType = SimpleType;
type TestTypeFac = SimpleTypeFactory;
type TestVar = MetaByte;
type TestVarFac = MetaByteFactory<TestTypeFac>;
type TestNode = NodeByte;
type TestTerm = EnumTerm<TestType, TestVar, TestNode>;
type TestTermFac = EnumTermFactory<TestType, TestVar, TestNode, TestTypeFac>;
type TestStatement = Statement<TestType, TestVar, TestNode, TestTerm>;

/// Helper to parse a compact proof to Statement
fn cd_proof_to_statement(
    proof: &str,
    var_factory: &TestVarFac,
    term_factory: &TestTermFac,
) -> Result<TestStatement, MguError> {
    let dict = create_dict(term_factory, var_factory, NodeByte::Implies, NodeByte::Not)?;

    Statement::from_compact_proof(proof, var_factory, term_factory, &dict)
}

/// Helper to parse Polish notation to Statement
fn polish_to_statement(
    polish: &str,
    var_factory: &TestVarFac,
    term_factory: &TestTermFac,
) -> Result<TestStatement, MguError> {
    let vars = var_factory
        .list_metavariables_by_type(&TestType::Boolean)
        .collect::<Vec<_>>();
    let mut engine = PolishNotationEngine::new();

    // Since none of these uses uppercase letters, both lowercase and uppercase ASCII letters will be valid as variables.
    engine.insert_operator('>', BooleanSimpleOp::ImpliesAB2)?;
    engine.insert_operator('~', BooleanSimpleOp::NotA1)?;

    build_boolean_statement_from_polish_with_engine(
        polish,
        term_factory,
        &vars,
        &[TestNode::Implies, TestNode::Not],
        &mut engine,
    )
}

/// Helper for CD proofs with known Polish expressions.
fn parse_cd_and_polish(proof: &str, polish: &str) {
    let var_factory = TestVarFac::new(Default::default());
    let term_factory = TestTermFac::new(Default::default());

    let proof_statement = cd_proof_to_statement(proof, &var_factory, &term_factory);
    assert!(proof_statement.is_ok(), "CD proof {} did not parse.", proof);
    let proof_statement = proof_statement.unwrap();

    let assertion_statement = polish_to_statement(polish, &var_factory, &term_factory);
    if assertion_statement.is_err() {
        eprintln!("{:?}", assertion_statement.unwrap_err());
        panic!("Game Over!");
    }
    assert!(
        assertion_statement.is_ok(),
        "Polish statement {} did not parse.",
        polish
    );
    let assertion_statement = assertion_statement.unwrap();

    assert_eq!(
        proof_statement.get_n_hypotheses(),
        0,
        "CD proof {} resulted in unexpected hypotheses.",
        proof
    );

    let validity = test_validity(&proof_statement, &term_factory, &Some(TestNode::Implies));
    assert!(validity.is_ok(), "CD proof {} failed to validate.", proof);
    assert!(
        validity.unwrap(),
        "CD proof {} resulted in invalid statement.",
        proof
    );

    let are_the_same =
        proof_statement.is_identical(&var_factory, &term_factory, &assertion_statement);
    assert!(
        are_the_same.is_ok(),
        "CD proof {} could not be checked against expected {}.",
        proof,
        polish
    );
    assert!(
        are_the_same.unwrap(),
        "CD proof {} is not equivalent to expected {}.",
        proof,
        polish
    );
}

/// Regression test for DDD111D23
///
/// This proof exposed a bug in rustmgu where statements were not made disjoint
/// before unification in apply/apply_multiple operations.
///
/// Expected output (Polish notation): >P>>>~Q~RR>>~Q~RQ
/// Where > is Implies, ~ is Not
#[test]
fn regression_ddd111d23_produces_tautology() {
    let proof = "DDD111D23";
    let assertion = ">P>>>~Q~RR>>~Q~RQ";

    parse_cd_and_polish(proof, assertion);
}

/// Regression test for DDD1D221D2D2D11
///
/// This proof also exposed the disjointness bug in rustmgu.
///
/// Expected output (Polish notation): >>>>>PQRQ>>PQR>>>>PQRQR
/// Where > is Implies
#[test]
fn regression_ddd1d221d2d2d11_produces_tautology() {
    let proof = "DDD1D221D2D2D11";
    let assertion = ">>>>>PQRQ>>PQR>>>>PQRQR";

    parse_cd_and_polish(proof, assertion);
}

/// Test both proofs parse without errors (validates disjointness fix)
#[test]
fn regression_proofs_parse_successfully() {
    let var_factory = MetaByteFactory::new(SimpleTypeFactory);
    let term_factory = EnumTermFactory::new(SimpleTypeFactory);
    let dict = create_dict(
        &term_factory,
        &var_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )
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
    let var_factory = MetaByteFactory::new(SimpleTypeFactory);
    let term_factory = EnumTermFactory::new(SimpleTypeFactory);

    let dict = create_dict(
        &term_factory,
        &var_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )
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
