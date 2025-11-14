//! Tests for Statement::convert() cross-implementation conversion.

use itertools::Itertools;
use symbolic_mgu::{
    EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, MguError, NodeByte,
    NodeByteFactory, SimpleType, Statement, Term, TermFactory, WideMetavariable,
    WideMetavariableFactory,
};

type MetaByteStatement =
    Statement<SimpleType, MetaByte, NodeByte, EnumTerm<SimpleType, MetaByte, NodeByte>>;
type WideStatement = Statement<
    SimpleType,
    WideMetavariable,
    NodeByte,
    EnumTerm<SimpleType, WideMetavariable, NodeByte>,
>;

#[test]
fn convert_simple_axiom_metabyte_to_wide() -> Result<(), MguError> {
    // Create a simple statement with MetaByte
    let var_factory = MetaByteFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get first Boolean variable from factory iterator
    let p = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let p_term = term_factory.create_leaf(p)?;
    let stmt = Statement::new(p_term, vec![], Default::default())?;

    // Convert to WideMetavariable
    let wide_var_factory = WideMetavariableFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let wide_term_factory = EnumTermFactory::new();

    let converted: WideStatement =
        stmt.convert(&wide_var_factory, &node_factory, &wide_term_factory)?;

    // Verify the conversion preserved structure
    assert_eq!(converted.get_n_hypotheses(), 0);
    assert!(converted.get_assertion().is_metavariable());

    Ok(())
}

#[test]
fn convert_simple_axiom_wide_to_metabyte() -> Result<(), MguError> {
    // Create a simple statement with WideMetavariable
    let wide_var_factory = WideMetavariableFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get first Boolean variable from factory iterator
    let phi = wide_var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let phi_term = term_factory.create_leaf(phi)?;
    let stmt = Statement::new(phi_term, vec![], Default::default())?;

    // Convert to MetaByte
    let metabyte_var_factory = MetaByteFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let metabyte_term_factory = EnumTermFactory::new();

    let converted: MetaByteStatement =
        stmt.convert(&metabyte_var_factory, &node_factory, &metabyte_term_factory)?;

    // Verify the conversion preserved structure
    assert_eq!(converted.get_n_hypotheses(), 0);
    assert!(converted.get_assertion().is_metavariable());

    Ok(())
}

#[test]
fn convert_implication_with_hypotheses() -> Result<(), MguError> {
    // Create a more complex statement: (P → Q; P) using MetaByte
    let var_factory = MetaByteFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get first two Boolean variables using tuples()
    let (p_var, q_var) = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .tuples()
        .next()
        .unwrap();

    let p = term_factory.create_leaf(p_var)?;
    let q = term_factory.create_leaf(q_var)?;
    let p_implies_q = term_factory.create_node(NodeByte::Implies, vec![p.clone(), q])?;

    let stmt = Statement::new(p_implies_q, vec![p], Default::default())?;

    // Convert to WideMetavariable
    let wide_var_factory = WideMetavariableFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let wide_term_factory = EnumTermFactory::new();

    let converted: WideStatement =
        stmt.convert(&wide_var_factory, &node_factory, &wide_term_factory)?;

    // Verify structure preserved
    assert_eq!(converted.get_n_hypotheses(), 1);
    assert!(!converted.get_assertion().is_metavariable());
    assert!(converted.get_hypotheses()[0].is_metavariable());

    Ok(())
}

#[test]
fn convert_exhaustion_error() -> Result<(), MguError> {
    // Create a statement with 12 Boolean variables (more than MetaByte's limit of 11)
    let wide_var_factory = WideMetavariableFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get 12 Boolean variables from WideMetavariable
    let vars: Vec<_> = wide_var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .take(12)
        .collect();

    // Create a complex term using all 12 variables
    let mut assertion = term_factory.create_leaf(vars[0]).unwrap();
    for var in &vars[1..] {
        let leaf = term_factory.create_leaf(*var).unwrap();
        assertion = term_factory
            .create_node(NodeByte::And, vec![assertion, leaf])
            .unwrap();
    }

    let stmt = Statement::new(assertion, vec![], Default::default())?;

    // Try to convert to MetaByte (should fail with exhaustion error)
    let metabyte_var_factory = MetaByteFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let metabyte_term_factory = EnumTermFactory::new();

    let result: Result<MetaByteStatement, MguError> =
        stmt.convert(&metabyte_var_factory, &node_factory, &metabyte_term_factory);

    // Should fail with AllocationError (exhaustion)
    assert!(result.is_err());
    match result {
        Err(MguError::AllocationError(msg)) => {
            assert!(msg.contains("exhausted"));
        }
        _ => panic!("Expected AllocationError for exhausted implementation"),
    }

    Ok(())
}

#[test]
fn convert_preserves_distinctness_graph() -> Result<(), MguError> {
    use symbolic_mgu::DistinctnessGraph;

    // Create a statement with distinctness constraints
    let var_factory = MetaByteFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get first two Setvar variables using tuples()
    let (x, y) = var_factory
        .list_metavariables_by_type(&SimpleType::Setvar)
        .tuples()
        .next()
        .unwrap();

    let x_term = term_factory.create_leaf(x)?;
    let y_term = term_factory.create_leaf(y)?;

    let mut distinctness = DistinctnessGraph::new();
    distinctness.add_edge(&x, &y)?;

    let stmt = Statement::new(x_term, vec![y_term], distinctness)?;

    // Convert to WideMetavariable
    let wide_var_factory = WideMetavariableFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let wide_term_factory = EnumTermFactory::new();

    let converted: WideStatement =
        stmt.convert(&wide_var_factory, &node_factory, &wide_term_factory)?;

    // Verify distinctness graph has edges
    let edges: Vec<_> = converted.get_distinctness_graph().edges_iter().collect();
    assert_eq!(edges.len(), 1, "Should have exactly one distinctness edge");

    Ok(())
}

#[test]
fn convert_round_trip() -> Result<(), MguError> {
    // Create a statement, convert it twice, verify structure preserved
    let var_factory = MetaByteFactory();
    let term_factory: EnumTermFactory<SimpleType, _, NodeByte> = EnumTermFactory::new();

    // Get first two Boolean variables using tuples()
    let (p_var, q_var) = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .tuples()
        .next()
        .unwrap();

    let p = term_factory.create_leaf(p_var)?;
    let q = term_factory.create_leaf(q_var)?;
    let p_and_q = term_factory.create_node(NodeByte::And, vec![p.clone(), q.clone()])?;

    let original = Statement::new(p_and_q, vec![p, q], Default::default())?;

    // Convert MetaByte → WideMetavariable
    let wide_var_factory = WideMetavariableFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let wide_term_factory = EnumTermFactory::new();

    let converted_to_wide: WideStatement =
        original.convert(&wide_var_factory, &node_factory, &wide_term_factory)?;

    // Convert WideMetavariable → MetaByte
    let metabyte_var_factory = MetaByteFactory();
    let metabyte_term_factory = EnumTermFactory::new();

    let converted_back: MetaByteStatement =
        converted_to_wide.convert(&metabyte_var_factory, &node_factory, &metabyte_term_factory)?;

    // Verify structure preserved
    assert_eq!(
        converted_back.get_n_hypotheses(),
        original.get_n_hypotheses()
    );
    assert_eq!(
        converted_back.get_assertion().is_metavariable(),
        original.get_assertion().is_metavariable()
    );

    Ok(())
}
