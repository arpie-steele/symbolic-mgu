//! Rules for Propositional Logic in the C-N basis.

use crate::logic::require_var_is_boolean;
use crate::{
    DistinctnessGraph, Metavariable, MguError, Node, Statement, Term, TermFactory, Type,
    TypeFactory,
};

/// Index of the minor premise (φ) in Modus Ponens hypotheses.
///
/// Modus Ponens has hypotheses `[φ, (φ → ψ)]`, so the minor premise φ is at index 0.
pub const MP_MINOR_PREMISE: usize = 0;

/// Index of the major premise (φ → ψ) in Modus Ponens hypotheses.
///
/// Modus Ponens has hypotheses `[φ, (φ → ψ)]`, so the major premise (φ → ψ) is at index 1.
pub const MP_MAJOR_PREMISE: usize = 1;

/// Build the Modus Ponens inference rule.
///
/// Modus Ponens: From φ and (φ → ψ), derive ψ
///
/// As a Statement: (ψ; φ, (φ → ψ); ∅)
///
/// # Arguments
///
/// * `phi_var` - Metavariable for φ (must be Boolean type)
/// * `psi_var` - Metavariable for ψ (must be Boolean type)
/// * `implies_node` - Node representing the implication operator (→)
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::propositional::rules::cn_basis::modus_ponens;
/// use symbolic_mgu::{EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, Metavariable, NodeByte, SimpleType, SimpleTypeFactory};
/// use itertools::Itertools;
/// use SimpleType::*;
///
/// // Create factory for building terms
/// let factory = EnumTermFactory::new(SimpleTypeFactory);
///
/// // Get two boolean metavariables
/// let vars = MetaByteFactory::new(SimpleTypeFactory);
/// let (phi, psi) = vars.list_metavariables_by_type(&Boolean).tuples().next().unwrap();
///
/// // Create Modus Ponens: (ψ; φ, (φ → ψ); ∅)
/// let mp = modus_ponens(&factory, phi, psi, NodeByte::Implies).unwrap();
///
/// assert_eq!(mp.get_n_hypotheses(), 2);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn modus_ponens<Ty, V, N, T, TF, TyF>(
    factory: &TF,
    phi_var: V,
    psi_var: V,
    implies_node: N,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
    TyF: TypeFactory<Type = Ty>,
{
    // Verify both variables are Boolean
    require_var_is_boolean(factory.type_factory(), &phi_var)?;
    require_var_is_boolean(factory.type_factory(), &psi_var)?;

    // Build terms for φ and ψ
    let phi = factory.create_leaf(phi_var.clone())?;
    let psi = factory.create_leaf(psi_var.clone())?;

    // Build (φ → ψ)
    let phi_implies_psi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), psi.clone()])?;

    // Assertion: ψ
    let assertion = psi;

    // Hypotheses: φ, (φ → ψ)
    let hypotheses = vec![phi, phi_implies_psi];

    // No distinctness constraints
    let dist_graph = DistinctnessGraph::default();

    Statement::new(factory.type_factory(), assertion, hypotheses, dist_graph)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_eval::BooleanSimpleNode;
    use crate::bool_eval::BooleanSimpleOp::ImpliesAB2;
    use crate::logic::build_boolean_statement_from_polish;
    use crate::{
        EnumTermFactory, MetavariableFactory, SimpleType, SimpleTypeFactory,
        WideMetavariableFactory,
    };

    type MyType = SimpleType;
    type MyNode = BooleanSimpleNode<MyType>;

    #[test]
    fn modus_ponens_equals_polish() {
        let var_factory = WideMetavariableFactory::new(SimpleTypeFactory);
        let vars = var_factory
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new(SimpleTypeFactory);

        let from_builder = modus_ponens(
            &factory,
            vars[0],
            vars[1],
            MyNode::from_op(ImpliesAB2, SimpleType::Boolean),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "p;Cpq;q",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2, SimpleType::Boolean)],
        )
        .unwrap();

        assert_eq!(
            from_builder
                .canonicalize(&var_factory, &factory)
                .unwrap()
                .get_assertion(),
            from_polish.get_assertion()
        );

        assert_ne!(
            from_builder.get_assertion().get_metavariable().unwrap(),
            from_builder
                .get_hypothesis(MP_MINOR_PREMISE)
                .unwrap()
                .get_metavariable()
                .unwrap()
        );

        assert_ne!(
            from_polish.get_assertion().get_metavariable().unwrap(),
            from_polish
                .get_hypothesis(MP_MINOR_PREMISE)
                .unwrap()
                .get_metavariable()
                .unwrap()
        );

        assert_eq!(
            from_builder.get_assertion().get_node(),
            from_polish.get_assertion().get_node()
        );
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );

        for i in 0..from_builder.get_n_hypotheses() {
            assert_eq!(
                from_builder.get_hypothesis(i).unwrap().get_node(),
                from_polish.get_hypothesis(i).unwrap().get_node()
            );
        }

        assert_eq!(
            from_builder.is_identical(&var_factory, &factory, &from_polish),
            Ok(true)
        );
    }

    #[test]
    fn modus_ponens_constants() {
        let vars = WideMetavariableFactory::new(SimpleTypeFactory)
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new(SimpleTypeFactory);

        let mp = modus_ponens(
            &factory,
            vars[0],
            vars[1],
            MyNode::from_op(ImpliesAB2, SimpleType::Boolean),
        )
        .unwrap();

        // Verify the index constants are correct
        assert_eq!(
            mp.get_hypothesis(MP_MINOR_PREMISE)
                .unwrap()
                .get_metavariable(),
            Some(vars[0])
        );
        assert!(mp
            .get_hypothesis(MP_MAJOR_PREMISE)
            .unwrap()
            .get_node()
            .is_some());
        assert_eq!(mp.get_assertion().get_metavariable(), Some(vars[1]));
    }
}
