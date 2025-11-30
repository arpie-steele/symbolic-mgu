//! Definitions for Propositional Calculus in the C-N basis.
//!
//! "C" here refers to material implication and "N" to the not operator.

use crate::logic::require_var_is_boolean;
use crate::{Metavariable, MguError, Node, Statement, Term, TermFactory, Type};

/// Build the (disguised) definition: ¬ (((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))) → ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))
///
/// This is the same as ((𝜑 ↔ 𝜓) ↔ ((𝜑 → 𝜓) ∧ (𝜓 → 𝜑))) with expansion of the second `↔` and all the `∧` symbols in terms of `→` and `¬`.
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn define_biimp<Ty, V, N, T, TF>(
    factory: &TF,
    biimp_node: N,
    phi_var: V,
    psi_var: V,
    not_node: N,
    implies_node: N,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;

    // Build terms for φ and ψ
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;

    // Build(𝜑 ↔ 𝜓)
    let equivalence = factory.create_node(biimp_node, vec![phi.clone(), psi.clone()])?;

    // Build (𝜑 → 𝜓)
    let fore = factory.create_node(implies_node.clone(), vec![phi.clone(), psi.clone()])?;

    // Build (𝜓 → 𝜑)
    let back = factory.create_node(implies_node.clone(), vec![psi, phi])?;

    // Build ¬ (𝜓 → 𝜑)
    let not_back = factory.create_node(not_node.clone(), vec![back])?;

    // Build((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))
    let fore_nand_back = factory.create_node(implies_node.clone(), vec![fore, not_back])?;

    // Build ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))
    let fore_and_back = factory.create_node(not_node.clone(), vec![fore_nand_back])?;

    // Build ((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)))
    let equivalence_implies_fore_and_back = factory.create_node(
        implies_node.clone(),
        vec![equivalence.clone(), fore_and_back.clone()],
    )?;

    // Build (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓))
    let fore_and_back_implies_equivalence =
        factory.create_node(implies_node.clone(), vec![fore_and_back, equivalence])?;

    // Build ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓))
    let fore_and_back_and_not_equivalence =
        factory.create_node(not_node.clone(), vec![fore_and_back_implies_equivalence])?;

    // Build (((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))) → ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))
    let equivalence_xor_fore_and_back = factory.create_node(
        implies_node.clone(),
        vec![
            equivalence_implies_fore_and_back,
            fore_and_back_and_not_equivalence,
        ],
    )?;

    // Build ¬ (((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))) → ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))
    let assertion = factory.create_node(not_node, vec![equivalence_xor_fore_and_back])?;

    Statement::simple_axiom(assertion)
}

/// Build the definition: ((𝜑 ∧ 𝜓) ↔ ¬ (𝜑 → ¬ 𝜓))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn define_and<Ty, V, N, T, TF>(
    factory: &TF,
    and_node: N,
    phi_var: V,
    psi_var: V,
    biimp_node: N,
    not_node: N,
    implies_node: N,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;

    // Build terms for φ and ψ
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;

    // Build (𝜑 ∧ 𝜓)
    let left = factory.create_node(and_node, vec![phi.clone(), psi.clone()])?;

    // Build ¬ 𝜓
    let not_psi = factory.create_node(not_node.clone(), vec![psi])?;

    // Build (𝜑 → ¬ 𝜓)
    let phi_nand_psi = factory.create_node(implies_node, vec![phi, not_psi])?;

    // Build ¬ (𝜑 → ¬ 𝜓)
    let right = factory.create_node(not_node, vec![phi_nand_psi])?;

    // Build ((𝜑 ∧ 𝜓) ↔ ¬ (𝜑 → ¬ 𝜓))
    let assertion = factory.create_node(biimp_node, vec![left, right])?;

    Statement::simple_axiom(assertion)
}

/// Build the definition: ((𝜑 ∨ 𝜓) ↔ (¬ 𝜑 → 𝜓))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn define_or<Ty, V, N, T, TF>(
    factory: &TF,
    or_node: N,
    phi_var: V,
    psi_var: V,
    biimp_node: N,
    not_node: N,
    implies_node: N,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;

    // Build terms for φ and ψ
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;

    // Build (𝜑 ∨ 𝜓)
    let left = factory.create_node(or_node, vec![phi.clone(), psi.clone()])?;

    // Build ¬ 𝜑
    let not_phi = factory.create_node(not_node, vec![phi])?;

    // Build (¬ 𝜑 → 𝜓)
    let right = factory.create_node(implies_node, vec![not_phi, psi])?;

    // Build ((𝜑 ∨ 𝜓) ↔ (¬ 𝜑 → 𝜓))
    let assertion = factory.create_node(biimp_node, vec![left, right])?;

    Statement::simple_axiom(assertion)
}

/*
df-ifp 1063	⊢ (if-(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ∧ 𝜓) ∨ (¬ 𝜑 ∧ 𝜒)))


df-3or 1087	⊢ ((𝜑 ∨ 𝜓 ∨ 𝜒) ↔ ((𝜑 ∨ 𝜓) ∨ 𝜒))
df-3an 1088	⊢ ((𝜑 ∧ 𝜓 ∧ 𝜒) ↔ ((𝜑 ∧ 𝜓) ∧ 𝜒))

df-nan 1492	⊢ ((𝜑 ⊼ 𝜓) ↔ ¬ (𝜑 ∧ 𝜓))

df-xor 1512	⊢ ((𝜑 ⊻ 𝜓) ↔ ¬ (𝜑 ↔ 𝜓))

df-nor 1529	⊢ ((𝜑 ⊽ 𝜓) ↔ ¬ (𝜑 ∨ 𝜓))


df-tru 1543	⊢ (⊤ ↔ (∀𝑥 𝑥 = 𝑥 → ∀𝑥 𝑥 = 𝑥))

df-fal 1553	⊢ (⊥ ↔ ¬ ⊤)

df-had 1594	⊢ (hadd(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ⊻ 𝜓) ⊻ 𝜒))

df-cad 1607	⊢ (cadd(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ∧ 𝜓) ∨ (𝜒 ∧ (𝜑 ⊻ 𝜓))))

 */

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_eval::BooleanSimpleOp::{AndAB2, BiimpAB2, ImpliesAB2, NotA1, OrAB2};
    use crate::bool_eval::{test_tautology, BooleanSimpleNode};
    use crate::{EnumTermFactory, MetavariableFactory, SimpleType, WideMetavariableFactory};
    use itertools::Itertools;

    type MyType = SimpleType;
    type MyNode = BooleanSimpleNode<MyType>;

    #[test]
    fn define_biimp_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = define_biimp(
            &factory,
            MyNode::from_op(BiimpAB2),
            phi,
            psi,
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn define_and_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = define_and(
            &factory,
            MyNode::from_op(AndAB2),
            phi,
            psi,
            MyNode::from_op(BiimpAB2),
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn define_or_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = define_or(
            &factory,
            MyNode::from_op(OrAB2),
            phi,
            psi,
            MyNode::from_op(BiimpAB2),
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }
}
