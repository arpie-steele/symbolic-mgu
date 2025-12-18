//! Validate the capability-based Type system design.
//!
//! This test suite ensures that the Type trait's capability methods
//! (`try_boolean()`, `try_setvar()`, `try_class()`) work correctly and
//! that generic code can check for capabilities before using them.
//!
//! The design allows type systems to opt-in to only the types they support:
//! - Pure propositional logic: Only Boolean
//! - First-order logic: Boolean + Setvar + Class
//! - Custom type hierarchies: Domain-specific types
//!
//! This provides "pay for what you use" semantics at the type system level.

use symbolic_mgu::{
    EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, Metavariable, MetavariableFactory,
    MguError, Node, NodeByte, SimpleType, Statement, Term, TermFactory, Type, TypeCore,
};
use SimpleType::*;

/// Test that SimpleType supports all three base types
#[test]
fn simple_type_supports_all_capabilities() {
    // Boolean should succeed
    let boolean = SimpleType::try_boolean();
    assert!(boolean.is_ok());
    assert_eq!(boolean.unwrap(), Boolean);

    // Setvar should succeed
    let setvar = SimpleType::try_setvar();
    assert!(setvar.is_ok());
    assert_eq!(setvar.unwrap(), Setvar);

    // Class should succeed
    let class = SimpleType::try_class();
    assert!(class.is_ok());
    assert_eq!(class.unwrap(), Class);
}

/// Test that capability methods are consistent with type identity
#[test]
fn capability_methods_match_types() -> Result<(), MguError> {
    let boolean = SimpleType::try_boolean()?;
    let setvar = SimpleType::try_setvar()?;
    let class = SimpleType::try_class()?;

    // Each type should be distinct
    assert_ne!(boolean, setvar);
    assert_ne!(boolean, class);
    assert_ne!(setvar, class);

    Ok(())
}

/// Test subtyping relationships
#[test]
fn subtyping_relationships() -> Result<(), MguError> {
    let boolean = SimpleType::try_boolean()?;
    let setvar = SimpleType::try_setvar()?;
    let class = SimpleType::try_class()?;

    // Boolean is subtype of Boolean
    assert!(boolean.is_subtype_of(&boolean));

    // Setvar is subtype of Class (in Metamath)
    assert!(setvar.is_subtype_of(&class));

    // Setvar is subtype of Setvar
    assert!(setvar.is_subtype_of(&setvar));

    // Class is subtype of Class
    assert!(class.is_subtype_of(&class));

    // Boolean is NOT a subtype of Setvar
    assert!(!boolean.is_subtype_of(&setvar));

    // Boolean is NOT a subtype of Class
    assert!(!boolean.is_subtype_of(&class));

    // Class is NOT a subtype of Setvar
    assert!(!class.is_subtype_of(&setvar));

    Ok(())
}

/// Test that type checking methods work correctly
#[test]
fn type_checking_methods() -> Result<(), MguError> {
    let boolean = SimpleType::try_boolean()?;
    let setvar = SimpleType::try_setvar()?;
    let class = SimpleType::try_class()?;

    // Test is_boolean()
    assert!(boolean.is_boolean());
    assert!(!setvar.is_boolean());
    assert!(!class.is_boolean());

    // Test is_setvar()
    assert!(!boolean.is_setvar());
    assert!(setvar.is_setvar());
    assert!(!class.is_setvar());

    // Test is_class()
    assert!(!boolean.is_class());
    assert!(!setvar.is_class());
    assert!(class.is_class());

    Ok(())
}

/// Tests demonstrating how generic code should check capabilities

/// Example of generic code that checks for Boolean capability before use
fn create_boolean_term<T, V, N, F>(
    factory: &mut F,
    var_factory: &impl MetavariableFactory<MetavariableType = T, Metavariable = V>,
) -> Result<EnumTerm<T, V, N>, MguError>
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
    F: TermFactory<EnumTerm<T, V, N>, T, V, N, Term = EnumTerm<T, V, N>, TermMetavariable = V>,
{
    // Check if Boolean type is supported
    let bool_type = T::try_boolean()?;

    // If we get here, Boolean is supported - proceed
    let var = var_factory
        .list_metavariables_by_type(&bool_type)
        .next()
        .ok_or_else(|| MguError::from_type_and_var_strings("Boolean", "P"))?;

    factory.create_leaf(var)
}

/// Test that capability checking works in practice
#[test]
fn capability_checking_in_generic_code() -> Result<(), MguError> {
    let mut term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // This should succeed because SimpleType supports Boolean
    let result = create_boolean_term(&mut term_factory, &var_factory);
    assert!(result.is_ok());

    let term = result?;
    assert!(term.is_metavariable());
    assert_eq!(term.get_type()?, Boolean);

    Ok(())
}

/// Test creating terms with different types
#[test]
fn create_terms_with_all_types() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // Boolean variable
    let bool_var = var_factory
        .list_metavariables_by_type(&SimpleType::try_boolean()?)
        .next()
        .unwrap();
    let bool_term = term_factory.create_leaf(bool_var)?;
    assert_eq!(bool_term.get_type()?, Boolean);

    // Setvar variable
    let setvar = var_factory
        .list_metavariables_by_type(&SimpleType::try_setvar()?)
        .next()
        .unwrap();
    let setvar_term = term_factory.create_leaf(setvar)?;
    assert_eq!(setvar_term.get_type()?, Setvar);

    // Class variable
    let class_var = var_factory
        .list_metavariables_by_type(&SimpleType::try_class()?)
        .next()
        .unwrap();
    let class_term = term_factory.create_leaf(class_var)?;
    assert_eq!(class_term.get_type()?, Class);

    Ok(())
}

/// Test that statements validate Boolean type for assertions
#[test]
fn statements_require_boolean_assertions() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let bool_var = var_factory
        .list_metavariables_by_type(&SimpleType::try_boolean()?)
        .next()
        .unwrap();
    let p = term_factory.create_leaf(bool_var)?;

    // Create p → p (Boolean type)
    let implies = term_factory.create_node(NodeByte::Implies, vec![p.clone(), p])?;

    // Should succeed - assertion is Boolean
    let stmt = Statement::simple_axiom(implies);
    assert!(stmt.is_ok());

    Ok(())
}

/// Test that non-Boolean assertions are rejected
#[test]
fn statements_reject_non_boolean_assertions() {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    // Create a Setvar term (not Boolean)
    let setvar = var_factory
        .list_metavariables_by_type(&Setvar)
        .next()
        .unwrap();
    let setvar_term = term_factory.create_leaf(setvar).unwrap();

    // Try to create statement with Setvar assertion (should fail)
    let stmt = Statement::simple_axiom(setvar_term);
    assert!(
        stmt.is_err(),
        "Statement with Setvar assertion should be rejected"
    );

    // Verify it's a type error (TypeMismatch or TypeUnassignable)
    if let Err(e) = stmt {
        match e {
            MguError::TypeMismatch(_, _) | MguError::TypeUnassignable(_, _) => {
                // Expected - type mismatch between Setvar and Boolean
            }
            _ => {
                panic!(
                    "Expected TypeMismatch or TypeUnassignable error, got: {:?}",
                    e
                );
            }
        }
    }
}

/// Test compound Boolean expressions
#[test]
fn compound_boolean_expressions() -> Result<(), MguError> {
    let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    let var_factory = MetaByteFactory();

    let p = var_factory
        .list_metavariables_by_type(&SimpleType::try_boolean()?)
        .next()
        .unwrap();
    let q = var_factory
        .list_metavariables_by_type(&SimpleType::try_boolean()?)
        .nth(1)
        .unwrap();

    let p_term = term_factory.create_leaf(p)?;
    let q_term = term_factory.create_leaf(q)?;

    // Create p ∧ q
    let and_term = term_factory.create_node(NodeByte::And, vec![p_term.clone(), q_term.clone()])?;
    assert_eq!(and_term.get_type()?, Boolean);

    // Create ¬p
    let not_term = term_factory.create_node(NodeByte::Not, vec![p_term.clone()])?;
    assert_eq!(not_term.get_type()?, Boolean);

    // Create (p ∧ q) → p
    let implies = term_factory.create_node(NodeByte::Implies, vec![and_term, p_term])?;
    assert_eq!(implies.get_type()?, Boolean);

    // Should be able to create statement from this
    let stmt = Statement::simple_axiom(implies)?;
    assert_eq!(stmt.get_n_hypotheses(), 0);

    Ok(())
}

/// Demonstrate the pattern: check capability before attempting to use it
#[test]
fn demonstrate_capability_check_pattern() {
    // Pattern 1: Check before use
    let supports_boolean = SimpleType::try_boolean().is_ok();
    assert!(supports_boolean, "SimpleType should support Boolean");

    let supports_setvar = SimpleType::try_setvar().is_ok();
    assert!(supports_setvar, "SimpleType should support Setvar");

    let supports_class = SimpleType::try_class().is_ok();
    assert!(supports_class, "SimpleType should support Class");

    // Pattern 2: Use Result to propagate capability errors
    fn needs_setvar_capability<T: Type>() -> Result<T, MguError> {
        T::try_setvar()
    }

    // Should succeed for SimpleType
    let result = needs_setvar_capability::<SimpleType>();
    assert!(result.is_ok());
}
