//! Property tests for Term trait invariants.
//!
//! These tests validate that all Term implementations maintain
//! core invariants across all possible constructions.

use symbolic_mgu::{
    EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, MguError, NodeByte,
    SimpleType, Term, TermFactory,
};

/// Test that get_n_children() matches get_children().count()
#[test]
fn children_count_invariant() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // Test leaf (metavariable)
    let var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let leaf: EnumTerm<SimpleType, MetaByte, NodeByte> = term_factory.create_leaf(var)?;
    assert_eq!(leaf.get_n_children(), leaf.get_children().count());
    assert_eq!(leaf.get_n_children(), 0);

    // Test nullary node (True)
    let nullary = term_factory.create_node(NodeByte::True, vec![])?;
    assert_eq!(nullary.get_n_children(), nullary.get_children().count());
    assert_eq!(nullary.get_n_children(), 0);

    // Test unary node (Not)
    let unary = term_factory.create_node(NodeByte::Not, vec![leaf.clone()])?;
    assert_eq!(unary.get_n_children(), unary.get_children().count());
    assert_eq!(unary.get_n_children(), 1);

    // Test binary node (And)
    let binary = term_factory.create_node(NodeByte::And, vec![leaf.clone(), leaf.clone()])?;
    assert_eq!(binary.get_n_children(), binary.get_children().count());
    assert_eq!(binary.get_n_children(), 2);

    // Test ternary node (LogicalIf)
    let ternary = term_factory.create_node(
        NodeByte::LogicalIf,
        vec![leaf.clone(), leaf.clone(), leaf.clone()],
    )?;
    assert_eq!(ternary.get_n_children(), ternary.get_children().count());
    assert_eq!(ternary.get_n_children(), 3);

    Ok(())
}

/// Test that get_child(i) matches get_children().nth(i)
#[test]
fn children_indexing_invariant() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let var1 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let var2 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .nth(1)
        .unwrap();
    let var3 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .nth(2)
        .unwrap();

    let leaf1 = term_factory.create_leaf(var1)?;
    let leaf2 = term_factory.create_leaf(var2)?;
    let leaf3 = term_factory.create_leaf(var3)?;

    // Test ternary node
    let ternary = term_factory.create_node(
        NodeByte::LogicalIf,
        vec![leaf1.clone(), leaf2.clone(), leaf3.clone()],
    )?;

    // Verify indexing matches iteration
    for i in 0..ternary.get_n_children() {
        let via_index = ternary.get_child(i);
        let via_iter = ternary.get_children().nth(i);
        assert_eq!(via_index, via_iter);
    }

    // Verify out-of-bounds returns None
    assert_eq!(ternary.get_child(100), None);

    Ok(())
}

/// Test that factory-constructed terms are always valid
#[test]
fn factory_terms_are_valid() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // Leaves should be valid
    let var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let leaf = term_factory.create_leaf(var)?;
    assert!(leaf.is_valid_sentence()?);

    // Nodes with correct arity should be valid
    let not_term = term_factory.create_node(NodeByte::Not, vec![leaf.clone()])?;
    assert!(not_term.is_valid_sentence()?);

    let and_term = term_factory.create_node(NodeByte::And, vec![leaf.clone(), leaf.clone()])?;
    assert!(and_term.is_valid_sentence()?);

    Ok(())
}

/// Test that get_type() returns the correct type for metavariables
#[test]
fn metavariable_type_consistency() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // Test Boolean metavariable
    let bool_var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let bool_leaf = term_factory.create_leaf(bool_var)?;
    assert_eq!(bool_leaf.get_type()?, SimpleType::Boolean);

    // Test Setvar metavariable
    let setvar = var_factory
        .list_metavariables_by_type(&SimpleType::Setvar)
        .next()
        .unwrap();
    let setvar_leaf = term_factory.create_leaf(setvar)?;
    assert_eq!(setvar_leaf.get_type()?, SimpleType::Setvar);

    // Test Class metavariable
    let class = var_factory
        .list_metavariables_by_type(&SimpleType::Class)
        .next()
        .unwrap();
    let class_leaf = term_factory.create_leaf(class)?;
    assert_eq!(class_leaf.get_type()?, SimpleType::Class);

    Ok(())
}

/// Test that get_type() returns the node's type for node applications
#[test]
fn node_type_consistency() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let bool_var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let leaf = term_factory.create_leaf(bool_var)?;

    // Boolean nodes return Boolean type
    let not_term = term_factory.create_node(NodeByte::Not, vec![leaf.clone()])?;
    assert_eq!(not_term.get_type()?, SimpleType::Boolean);

    let and_term = term_factory.create_node(NodeByte::And, vec![leaf.clone(), leaf.clone()])?;
    assert_eq!(and_term.get_type()?, SimpleType::Boolean);

    Ok(())
}

/// Test that collect_metavariables gathers all variables
#[test]
fn collect_metavariables_completeness() -> Result<(), MguError> {
    use std::collections::HashSet;

    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let var1 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let var2 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .nth(1)
        .unwrap();
    let var3 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .nth(2)
        .unwrap();

    // Test single variable
    let leaf1 = term_factory.create_leaf(var1)?;
    let mut vars = HashSet::new();
    leaf1.collect_metavariables(&mut vars)?;
    assert_eq!(vars.len(), 1);
    assert!(vars.contains(&var1));

    // Test multiple variables in a compound term
    let leaf2 = term_factory.create_leaf(var2)?;
    let leaf3 = term_factory.create_leaf(var3)?;

    let and_term = term_factory.create_node(NodeByte::And, vec![leaf2.clone(), leaf3.clone()])?;

    vars.clear();
    and_term.collect_metavariables(&mut vars)?;
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&var2));
    assert!(vars.contains(&var3));

    // Test nested term with duplicate variables: (var1 ∧ (var2 ∧ var1))
    let inner_and = term_factory.create_node(NodeByte::And, vec![leaf2.clone(), leaf1.clone()])?;
    let outer_and = term_factory.create_node(NodeByte::And, vec![leaf1.clone(), inner_and])?;

    vars.clear();
    outer_and.collect_metavariables(&mut vars)?;
    assert_eq!(vars.len(), 2); // var1 appears twice but should only be counted once
    assert!(vars.contains(&var1));
    assert!(vars.contains(&var2));

    Ok(())
}

/// Test that get_children_as_slice() matches get_children() iterator
#[test]
fn children_slice_matches_iterator() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let var1 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let var2 = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .nth(1)
        .unwrap();

    let leaf1 = term_factory.create_leaf(var1)?;
    let leaf2 = term_factory.create_leaf(var2)?;

    let and_term = term_factory.create_node(NodeByte::And, vec![leaf1, leaf2])?;

    // Compare slice to iterator
    let slice = and_term.get_children_as_slice();
    let vec: Vec<_> = and_term.get_children().collect();

    assert_eq!(slice.len(), vec.len());
    for (i, item) in vec.iter().enumerate() {
        assert_eq!(&slice[i], *item);
    }

    Ok(())
}

/// Test that is_metavariable() correctly identifies leaves
#[test]
fn is_metavariable_correctness() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();

    // Leaf should be identified as metavariable
    let leaf = term_factory.create_leaf(var)?;
    assert!(leaf.is_metavariable());
    assert!(leaf.get_metavariable().is_some());
    assert!(leaf.get_node().is_none());

    // Node should not be identified as metavariable
    let not_term = term_factory.create_node(NodeByte::Not, vec![leaf])?;
    assert!(!not_term.is_metavariable());
    assert!(not_term.get_metavariable().is_none());
    assert!(not_term.get_node().is_some());

    Ok(())
}

/// Test that get_metavariable() and get_node() are mutually exclusive
#[test]
fn metavariable_node_mutual_exclusion() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let var = var_factory
        .list_metavariables_by_type(&SimpleType::Boolean)
        .next()
        .unwrap();
    let leaf = term_factory.create_leaf(var)?;

    let node_term = term_factory.create_node(NodeByte::True, vec![])?;

    // Leaf has metavariable but no node
    assert!(leaf.get_metavariable().is_some());
    assert!(leaf.get_node().is_none());

    // Node term has node but no metavariable
    assert!(node_term.get_metavariable().is_none());
    assert!(node_term.get_node().is_some());

    Ok(())
}
