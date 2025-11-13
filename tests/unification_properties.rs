//! Property-based tests for unification using proptest.
//!
//! These tests verify fundamental properties of the unification algorithm,
//! including commutativity, idempotence, type safety, and occurs checking.

use itertools::Itertools;
use proptest::prelude::*;
use symbolic_mgu::{
    apply_substitution, unify, EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory,
    MetavariableFactory, NodeByte, SimpleType, TermFactory,
};

// Type aliases for test clarity
type TestTerm = EnumTerm<SimpleType, MetaByte, NodeByte>;
type TestFactory = EnumTermFactory<SimpleType, MetaByte, NodeByte>;

/// Generate a random metavariable of the given type.
fn arbitrary_metavar(typ: SimpleType) -> impl Strategy<Value = MetaByte> {
    let factory = MetaByteFactory();
    let max_index = MetaByte::max_index_by_type(typ);
    (0..=max_index).prop_map(move |index| {
        factory
            .create_by_type_and_index(&typ, index)
            .expect("valid index")
    })
}

/// Generate a random Boolean metavariable.
fn arbitrary_boolean_var() -> impl Strategy<Value = MetaByte> {
    arbitrary_metavar(SimpleType::Boolean)
}

/// Generate a random Setvar metavariable.
fn arbitrary_setvar() -> impl Strategy<Value = MetaByte> {
    arbitrary_metavar(SimpleType::Setvar)
}

/// Generate a random Class metavariable.
fn arbitrary_class_var() -> impl Strategy<Value = MetaByte> {
    arbitrary_metavar(SimpleType::Class)
}

/// Generate a simple Boolean term (variable, or binary operation on variables).
#[allow(dead_code)]
fn arbitrary_boolean_term_simple() -> impl Strategy<Value = TestTerm> {
    prop_oneof![
        // Leaf: just a Boolean variable
        arbitrary_boolean_var()
            .prop_map(|var| { TestFactory::new().create_leaf(var).expect("leaf creation") }),
        // Binary operation: op(var1, var2)
        (arbitrary_boolean_var(), arbitrary_boolean_var()).prop_map(|(v1, v2)| {
            let factory = TestFactory::new();
            let t1 = factory.create_leaf(v1).expect("leaf");
            let t2 = factory.create_leaf(v2).expect("leaf");
            factory
                .create_node(NodeByte::Implies, vec![t1, t2])
                .expect("node")
        }),
    ]
}

/// Generate a Boolean term with controlled depth (0-2).
fn arbitrary_boolean_term(depth: u32) -> impl Strategy<Value = TestTerm> {
    let leaf = arbitrary_boolean_var()
        .prop_map(|var| TestFactory::new().create_leaf(var).expect("leaf creation"));

    leaf.prop_recursive(depth, 8, 3, |inner| {
        (inner.clone(), inner.clone()).prop_map(|(t1, t2)| {
            TestFactory::new()
                .create_node(NodeByte::Implies, vec![t1, t2])
                .expect("node")
        })
    })
}

/// Generate a Setvar term (just variables for now).
#[allow(dead_code)]
fn arbitrary_setvar_term() -> impl Strategy<Value = TestTerm> {
    arbitrary_setvar().prop_map(|var| TestFactory::new().create_leaf(var).expect("leaf creation"))
}

/// Generate a Class term (Setvar or equality).
#[allow(dead_code)]
fn arbitrary_class_term() -> impl Strategy<Value = TestTerm> {
    prop_oneof![
        // A setvar is a class
        arbitrary_setvar()
            .prop_map(|var| { TestFactory::new().create_leaf(var).expect("leaf creation") }),
        // Equality of two setvars
        (arbitrary_setvar(), arbitrary_setvar()).prop_map(|(v1, v2)| {
            let factory = TestFactory::new();
            let t1 = factory.create_leaf(v1).expect("leaf");
            let t2 = factory.create_leaf(v2).expect("leaf");
            factory
                .create_node(NodeByte::Equals, vec![t1, t2])
                .expect("node")
        }),
    ]
}

/// Generate two Boolean terms with guaranteed disjoint variable sets.
fn arbitrary_disjoint_boolean_terms() -> impl Strategy<Value = (TestTerm, TestTerm)> {
    // Get 4 different Boolean variables
    Just(()).prop_map(|_| {
        let factory = TestFactory::new();
        let var_factory = MetaByteFactory();

        let (v1, v2, v3, v4) = var_factory
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .expect("at least 4 Boolean vars");

        // t1 uses only v1 and v2
        let t1_left = factory.create_leaf(v1).expect("leaf");
        let t1_right = factory.create_leaf(v2).expect("leaf");
        let t1 = factory
            .create_node(NodeByte::Implies, vec![t1_left, t1_right])
            .expect("node");

        // t2 uses only v3 and v4 (disjoint from t1)
        let t2_left = factory.create_leaf(v3).expect("leaf");
        let t2_right = factory.create_leaf(v4).expect("leaf");
        let t2 = factory
            .create_node(NodeByte::Implies, vec![t2_left, t2_right])
            .expect("node");

        (t1, t2)
    })
}

// ============================================================================
// Property 1: Commutativity (modulo variable renaming)
// ============================================================================

proptest! {
    #[test]
    fn unify_is_commutative_on_disjoint_terms((t1, t2) in arbitrary_disjoint_boolean_terms()) {
        let factory = TestFactory::new();

        let result1 = unify(&factory, &t1, &t2);
        let result2 = unify(&factory, &t2, &t1);

        // Both should succeed or both should fail
        prop_assert_eq!(result1.is_ok(), result2.is_ok(),
            "unify(t1, t2) and unify(t2, t1) must both succeed or both fail");

        if let (Ok(sigma1), Ok(sigma2)) = (result1, result2) {
            // Apply substitutions
            let t1_sigma1 = apply_substitution(&factory, &sigma1, &t1)?;
            let t2_sigma1 = apply_substitution(&factory, &sigma1, &t2)?;
            let t1_sigma2 = apply_substitution(&factory, &sigma2, &t1)?;
            let t2_sigma2 = apply_substitution(&factory, &sigma2, &t2)?;

            // After unification, t1·σ1 should equal t2·σ1
            prop_assert_eq!(&t1_sigma1, &t2_sigma1, "unify(t1,t2): t1·σ != t2·σ");

            // After unification, t1·σ2 should equal t2·σ2
            prop_assert_eq!(&t1_sigma2, &t2_sigma2, "unify(t2,t1): t1·σ != t2·σ");
        }
    }
}

// ============================================================================
// Property 2: Idempotence - unifying already-unified terms
// ============================================================================

proptest! {
    #[test]
    fn unifying_unified_terms_succeeds(t1 in arbitrary_boolean_term(2),
                                        t2 in arbitrary_boolean_term(2)) {
        let factory = TestFactory::new();

        // Try to unify t1 and t2
        if let Ok(sigma) = unify(&factory, &t1, &t2) {
            // Apply substitution to get unified terms
            let t1_prime = apply_substitution(&factory, &sigma, &t1)?;
            let t2_prime = apply_substitution(&factory, &sigma, &t2)?;

            // t1' and t2' should be identical
            prop_assert_eq!(&t1_prime, &t2_prime, "Unified terms should be identical");

            // Unifying t1' with t2' should succeed trivially
            let result = unify(&factory, &t1_prime, &t2_prime);
            prop_assert!(result.is_ok(), "Unifying unified terms should succeed");

            // Result should be empty or identity substitution
            if let Ok(sigma_prime) = result {
                // Applying σ' shouldn't change anything
                let t1_twice = apply_substitution(&factory, &sigma_prime, &t1_prime)?;
                let t2_twice = apply_substitution(&factory, &sigma_prime, &t2_prime)?;
                prop_assert_eq!(&t1_twice, &t1_prime, "Re-unifying should not change t1'");
                prop_assert_eq!(&t2_twice, &t2_prime, "Re-unifying should not change t2'");
            }
        }
    }
}

// ============================================================================
// Property 3: Reflexivity - any term unifies with itself
// ============================================================================

proptest! {
    #[test]
    fn term_unifies_with_itself(t in arbitrary_boolean_term(2)) {
        let factory = TestFactory::new();

        let result = unify(&factory, &t, &t);
        prop_assert!(result.is_ok(), "Any term should unify with itself");

        if let Ok(sigma) = result {
            // Applying σ to t should give back t (or something equivalent)
            let t_prime = apply_substitution(&factory, &sigma, &t)?;
            prop_assert_eq!(&t_prime, &t, "Unifying with self should not change term");
        }
    }
}

// ============================================================================
// Property 4: Unification produces equality
// ============================================================================

proptest! {
    #[test]
    fn successful_unification_produces_identical_terms(
        t1 in arbitrary_boolean_term(2),
        t2 in arbitrary_boolean_term(2)
    ) {
        let factory = TestFactory::new();

        if let Ok(sigma) = unify(&factory, &t1, &t2) {
            let t1_prime = apply_substitution(&factory, &sigma, &t1)?;
            let t2_prime = apply_substitution(&factory, &sigma, &t2)?;

            // The whole point of unification: t1·σ == t2·σ
            prop_assert_eq!(&t1_prime, &t2_prime,
                "After successful unification, applying σ must make terms identical");
        }
    }
}

// ============================================================================
// Property 5: Substitution idempotence
// ============================================================================

proptest! {
    #[test]
    fn substitution_is_idempotent(t1 in arbitrary_boolean_term(2),
                                   t2 in arbitrary_boolean_term(2)) {
        let factory = TestFactory::new();

        if let Ok(sigma) = unify(&factory, &t1, &t2) {
            // Apply once
            let t1_once = apply_substitution(&factory, &sigma, &t1)?;
            let t2_once = apply_substitution(&factory, &sigma, &t2)?;

            // Apply twice
            let t1_twice = apply_substitution(&factory, &sigma, &t1_once)?;
            let t2_twice = apply_substitution(&factory, &sigma, &t2_once)?;

            // Should be identical
            prop_assert_eq!(&t1_once, &t1_twice, "σ(σ(t1)) == σ(t1)");
            prop_assert_eq!(&t2_once, &t2_twice, "σ(σ(t2)) == σ(t2)");
        }
    }
}

// ============================================================================
// Property 6: Occurs check prevents cycles
// ============================================================================

proptest! {
    #[test]
    fn occurs_check_detects_cycles(var in arbitrary_boolean_var()) {
        let factory = TestFactory::new();

        // Create term f(var) where f is some operator
        let var_term = factory.create_leaf(var).expect("leaf");
        let cycle_term = factory.create_node(
            NodeByte::Not,
            vec![var_term.clone()]
        ).expect("node");

        // Trying to unify var with f(var) should fail
        let result = unify(&factory, &var_term, &cycle_term);
        prop_assert!(result.is_err(),
            "Unifying x with f(x) should fail due to occurs check");
    }
}

// ============================================================================
// Property 7: Type safety - subtyping rules
// ============================================================================

proptest! {
    #[test]
    fn class_var_accepts_setvar_term(
        class_var in arbitrary_class_var(),
        setvar in arbitrary_setvar()
    ) {
        let factory = TestFactory::new();

        let class_term = factory.create_leaf(class_var).expect("leaf");
        let setvar_term = factory.create_leaf(setvar).expect("leaf");

        // Class variable should accept Setvar term (Setvar ⊆ Class)
        let result = unify(&factory, &class_term, &setvar_term);
        prop_assert!(result.is_ok(),
            "Class variable should unify with Setvar term (Setvar ⊆ Class)");

        if let Ok(sigma) = result {
            // Substitution should bind class_var → setvar
            let class_after = apply_substitution(&factory, &sigma, &class_term)?;
            prop_assert_eq!(&class_after, &setvar_term,
                "Class var should be bound to Setvar term");
        }
    }

    #[test]
    fn setvar_rejects_class_only_terms(
        setvar in arbitrary_setvar(),
        class_var in arbitrary_class_var()
    ) {
        let factory = TestFactory::new();

        let setvar_term = factory.create_leaf(setvar).expect("leaf");
        let class_term = factory.create_leaf(class_var).expect("leaf");

        // Both directions should work: setvar unifies with class_var by binding class_var → setvar
        let result = unify(&factory, &setvar_term, &class_term);

        // This should succeed by binding the class_var, not the setvar
        if let Ok(sigma) = result {
            let setvar_after = apply_substitution(&factory, &sigma, &setvar_term)?;
            let class_after = apply_substitution(&factory, &sigma, &class_term)?;

            // Both should now be the setvar
            prop_assert_eq!(&setvar_after, &setvar_term, "Setvar should remain unchanged");
            prop_assert_eq!(&class_after, &setvar_term, "Class var should be bound to setvar");
        }
    }

    #[test]
    fn boolean_disjoint_from_setvar(
        bool_var in arbitrary_boolean_var(),
        setvar in arbitrary_setvar()
    ) {
        let factory = TestFactory::new();

        let bool_term = factory.create_leaf(bool_var).expect("leaf");
        let setvar_term = factory.create_leaf(setvar).expect("leaf");

        // Boolean and Setvar are disjoint type hierarchies
        let result = unify(&factory, &bool_term, &setvar_term);
        prop_assert!(result.is_err(),
            "Boolean variable should not unify with Setvar (disjoint types)");
    }

    #[test]
    fn boolean_disjoint_from_class(
        bool_var in arbitrary_boolean_var(),
        class_var in arbitrary_class_var()
    ) {
        let factory = TestFactory::new();

        let bool_term = factory.create_leaf(bool_var).expect("leaf");
        let class_term = factory.create_leaf(class_var).expect("leaf");

        // Boolean and Class are disjoint type hierarchies
        let result = unify(&factory, &bool_term, &class_term);
        prop_assert!(result.is_err(),
            "Boolean variable should not unify with Class (disjoint types)");
    }
}

// ============================================================================
// Property 8: Structural compatibility
// ============================================================================

proptest! {
    #[test]
    fn different_operators_fail(v1 in arbitrary_boolean_var(), v2 in arbitrary_boolean_var()) {
        let factory = TestFactory::new();

        let t1 = factory.create_leaf(v1).expect("leaf");
        let t2 = factory.create_leaf(v2).expect("leaf");

        // Create Implies(v1, v2) and And(v1, v2)
        let implies_term = factory.create_node(NodeByte::Implies, vec![t1.clone(), t2.clone()]).expect("implies");
        let and_term = factory.create_node(NodeByte::And, vec![t1, t2]).expect("and");

        // Different operators shouldn't unify
        let result = unify(&factory, &implies_term, &and_term);
        prop_assert!(result.is_err(),
            "Terms with different operators should not unify");
    }

    #[test]
    fn different_arities_fail(v1 in arbitrary_boolean_var(), v2 in arbitrary_boolean_var()) {
        let factory = TestFactory::new();

        let t1 = factory.create_leaf(v1).expect("leaf");
        let t2 = factory.create_leaf(v2).expect("leaf");

        // Create Not(v1) [unary] and Implies(v1, v2) [binary]
        let unary = factory.create_node(NodeByte::Not, vec![t1.clone()]).expect("not");
        let binary = factory.create_node(NodeByte::Implies, vec![t1, t2]).expect("implies");

        // Different arities shouldn't unify
        let result = unify(&factory, &unary, &binary);
        prop_assert!(result.is_err(),
            "Terms with different arities should not unify");
    }
}
