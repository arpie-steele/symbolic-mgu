//! Rules for Propositional Logic in the C-N basis.

use crate::logic::require_var_is_boolean;
use crate::{DistinctnessGraph, Metavariable, MguError, Node, Statement, Term, TermFactory, Type};

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
/// use symbolic_mgu::{EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, Metavariable, NodeByte, SimpleType};
/// use itertools::Itertools;
///
/// // Create factory for building terms
/// let factory = EnumTermFactory::new();
///
/// // Get two boolean metavariables
/// let vars = MetaByteFactory();
/// let (phi, psi) = vars.list_metavariables_by_type(&SimpleType::Boolean).tuples().next().unwrap();
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
pub fn modus_ponens<Ty, V, N, T, TF>(
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
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;

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

    Statement::new(assertion, hypotheses, dist_graph)
}
