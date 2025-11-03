//! Helper functions for building fundamental logic statements.
//!
//! This module provides builders for common logical axioms and rules
//! using the propositional calculus with Implies (→), Not (¬), and
//! Biimplication (↔).

use crate::{DistinctnessGraph, EnumTerm, Metavariable, MetavariableFactory, MguError, Node, Statement, SimpleType, TypeCore};
use itertools::Itertools;
use std::collections::HashMap;

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
/// use symbolic_mgu::logic::modus_ponens;
/// use symbolic_mgu::{MetaByte, Metavariable, NodeByte, SimpleType};
///
/// // Get two boolean metavariables
/// let mut vars = MetaByte::enumerate(SimpleType::Boolean);
/// let phi = vars.next().unwrap();
/// let psi = vars.next().unwrap();
///
/// // Create Modus Ponens: (ψ; φ, (φ → ψ); ∅)
/// let mp = modus_ponens(phi, psi, NodeByte::Implies).unwrap();
///
/// assert_eq!(mp.get_n_hypotheses(), 2);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn modus_ponens<V, N>(
    phi_var: V,
    psi_var: V,
    implies_node: N,
) -> Result<Statement<SimpleType, V, N, EnumTerm<SimpleType, V, N>>, MguError>
where
    V: Metavariable<Type = SimpleType> + Default,
    N: Node<Type = SimpleType>,
{
    // Get types of variables
    let phi_type = phi_var.get_type()?;
    let psi_type = psi_var.get_type()?;

    // Verify both are Boolean
    if !phi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &phi_type, &SimpleType::Boolean));
    }
    if !psi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &psi_type, &SimpleType::Boolean));
    }

    // Build terms for φ and ψ
    let phi = EnumTerm::Leaf(phi_var.clone());
    let psi = EnumTerm::Leaf(psi_var.clone());

    // Build (φ → ψ)
    let phi_implies_psi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![phi.clone(), psi.clone()],
    );

    // Assertion: ψ
    let assertion = psi;

    // Hypotheses: φ, (φ → ψ)
    let hypotheses = vec![phi, phi_implies_psi];

    // No distinctness constraints
    let dist_graph = DistinctnessGraph::default();

    Statement::new(assertion, hypotheses, dist_graph)
}

/// Build the Simp axiom: (φ → (ψ → φ))
///
/// This axiom states that from any proposition, you can derive an implication
/// that discards its hypothesis.
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
/// use symbolic_mgu::logic::simp;
/// use symbolic_mgu::{MetaByte, Metavariable, NodeByte, SimpleType};
///
/// let mut vars = MetaByte::enumerate(SimpleType::Boolean);
/// let phi = vars.next().unwrap();
/// let psi = vars.next().unwrap();
///
/// // Create Simp axiom: ((φ → (ψ → φ)); ∅; ∅)
/// let axiom = simp(phi, psi, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0); // It's an axiom
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn simp<V, N>(
    phi_var: V,
    psi_var: V,
    implies_node: N,
) -> Result<Statement<SimpleType, V, N, EnumTerm<SimpleType, V, N>>, MguError>
where
    V: Metavariable<Type = SimpleType> + Default,
    N: Node<Type = SimpleType>,
{
    // Get types of variables
    let phi_type = phi_var.get_type()?;
    let psi_type = psi_var.get_type()?;

    // Verify both are Boolean
    if !phi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &phi_type, &SimpleType::Boolean));
    }
    if !psi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &psi_type, &SimpleType::Boolean));
    }

    // Build terms for φ and ψ
    let phi = EnumTerm::Leaf(phi_var);
    let psi = EnumTerm::Leaf(psi_var);

    // Build (ψ → φ)
    let psi_implies_phi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![psi, phi.clone()],
    );

    // Build (φ → (ψ → φ))
    let assertion = EnumTerm::NodeOrLeaf(
        implies_node,
        vec![phi, psi_implies_phi],
    );

    Statement::simple_axiom(assertion)
}

/// Build the Frege axiom: ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
///
/// This axiom represents the distributivity of implication.
///
/// # Arguments
///
/// * `phi_var` - Metavariable for φ (must be Boolean type)
/// * `psi_var` - Metavariable for ψ (must be Boolean type)
/// * `chi_var` - Metavariable for χ (must be Boolean type)
/// * `implies_node` - Node representing the implication operator (→)
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::frege;
/// use symbolic_mgu::{MetaByte, Metavariable, NodeByte, SimpleType};
///
/// let mut vars = MetaByte::enumerate(SimpleType::Boolean);
/// let phi = vars.next().unwrap();
/// let psi = vars.next().unwrap();
/// let chi = vars.next().unwrap();
///
/// // Create Frege axiom (distributivity)
/// let axiom = frege(phi, psi, chi, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn frege<V, N>(
    phi_var: V,
    psi_var: V,
    chi_var: V,
    implies_node: N,
) -> Result<Statement<SimpleType, V, N, EnumTerm<SimpleType, V, N>>, MguError>
where
    V: Metavariable<Type = SimpleType> + Default,
    N: Node<Type = SimpleType>,
{
    // Get types of variables
    let phi_type = phi_var.get_type()?;
    let psi_type = psi_var.get_type()?;
    let chi_type = chi_var.get_type()?;

    // Verify all are Boolean
    if !phi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &phi_type, &SimpleType::Boolean));
    }
    if !psi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &psi_type, &SimpleType::Boolean));
    }
    if !chi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &chi_type, &SimpleType::Boolean));
    }

    // Build terms for φ, ψ, χ
    let phi = EnumTerm::Leaf(phi_var);
    let psi = EnumTerm::Leaf(psi_var);
    let chi = EnumTerm::Leaf(chi_var);

    // Build (ψ → χ)
    let psi_implies_chi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![psi.clone(), chi.clone()],
    );

    // Build (φ → (ψ → χ))
    let phi_implies_psi_implies_chi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![phi.clone(), psi_implies_chi],
    );

    // Build (φ → ψ)
    let phi_implies_psi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![phi.clone(), psi],
    );

    // Build (φ → χ)
    let phi_implies_chi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![phi.clone(), chi.clone()],
    );

    // Build ((φ → ψ) → (φ → χ))
    let right_side = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![phi_implies_psi, phi_implies_chi],
    );

    // Build ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
    let assertion = EnumTerm::NodeOrLeaf(
        implies_node,
        vec![phi_implies_psi_implies_chi, right_side],
    );

    Statement::simple_axiom(assertion)
}

/// Build the Transp axiom: ((¬φ → ¬ψ) → (ψ → φ))
///
/// This axiom represents transposition (contrapositive).
///
/// # Arguments
///
/// * `phi_var` - Metavariable for φ (must be Boolean type)
/// * `psi_var` - Metavariable for ψ (must be Boolean type)
/// * `not_node` - Node representing the negation operator (¬)
/// * `implies_node` - Node representing the implication operator (→)
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::transp;
/// use symbolic_mgu::{MetaByte, Metavariable, NodeByte, SimpleType};
///
/// let mut vars = MetaByte::enumerate(SimpleType::Boolean);
/// let phi = vars.next().unwrap();
/// let psi = vars.next().unwrap();
///
/// // Create Transp axiom (contrapositive)
/// let axiom = transp(phi, psi, NodeByte::Not, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn transp<V, N>(
    phi_var: V,
    psi_var: V,
    not_node: N,
    implies_node: N,
) -> Result<Statement<SimpleType, V, N, EnumTerm<SimpleType, V, N>>, MguError>
where
    V: Metavariable<Type = SimpleType> + Default,
    N: Node<Type = SimpleType>,
{
    // Get types of variables
    let phi_type = phi_var.get_type()?;
    let psi_type = psi_var.get_type()?;

    // Verify both are Boolean
    if !phi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &phi_type, &SimpleType::Boolean));
    }
    if !psi_type.is_boolean() {
        return Err(MguError::from_found_and_expected_types(false, &psi_type, &SimpleType::Boolean));
    }

    // Build terms for φ and ψ
    let phi = EnumTerm::Leaf(phi_var);
    let psi = EnumTerm::Leaf(psi_var);

    // Build ¬φ
    let not_phi = EnumTerm::NodeOrLeaf(not_node.clone(), vec![phi.clone()]);

    // Build ¬ψ
    let not_psi = EnumTerm::NodeOrLeaf(not_node, vec![psi.clone()]);

    // Build (¬φ → ¬ψ)
    let not_phi_implies_not_psi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![not_phi, not_psi],
    );

    // Build (ψ → φ)
    let psi_implies_phi = EnumTerm::NodeOrLeaf(
        implies_node.clone(),
        vec![psi, phi],
    );

    // Build ((¬φ → ¬ψ) → (ψ → φ))
    let assertion = EnumTerm::NodeOrLeaf(
        implies_node,
        vec![not_phi_implies_not_psi, psi_implies_phi],
    );

    Statement::simple_axiom(assertion)
}

/// Type alias for statement dictionaries used in compact proof parsing.
pub type Dictionary<V, N> = HashMap<String, Statement<SimpleType, V, N, EnumTerm<SimpleType, V, N>>>;

/// Build standard statement dictionary for compact proofs.
///
/// Returns a HashMap mapping:
/// - `"D"` → Modus Ponens (detachment)
/// - `"1"` → Simp axiom
/// - `"2"` → Frege axiom
/// - `"3"` → Transp axiom
///
/// # Arguments
///
/// * `metavar_factory` - Factory for creating metavariables
/// * `implies_node` - Node representing the implication operator (→)
/// * `not_node` - Node representing the negation operator (¬)
///
/// # Examples
///
/// ```no_run
/// use symbolic_mgu::logic::create_dict;
/// use symbolic_mgu::{NodeByte, Metavariable, MetavariableFactory, SimpleType};
/// # fn example<MF>(factory: &MF)
/// # where
/// #     MF: MetavariableFactory<MetavariableType = SimpleType>,
/// #     MF::Metavariable: Metavariable<Type = SimpleType> + Default,
/// # {
///
/// let dict = create_dict(factory, NodeByte::Implies, NodeByte::Not).unwrap();
///
/// assert!(dict.contains_key("D"));  // Modus Ponens
/// assert!(dict.contains_key("1"));  // Simp
/// assert!(dict.contains_key("2"));  // Frege
/// assert!(dict.contains_key("3"));  // Transp
/// # }
/// ```
///
/// # Errors
///
/// Returns an error if statement construction fails or if there are insufficient
/// metavariables of Boolean type available.
pub fn create_dict<MF, N>(
    metavar_factory: &MF,
    implies_node: N,
    not_node: N,
) -> Result<Dictionary<MF::Metavariable, N>, MguError>
where
    MF: MetavariableFactory<MetavariableType = SimpleType>,
    MF::Metavariable: Metavariable<Type = SimpleType> + Default,
    N: Node<Type = SimpleType>,
{
    // Get three Boolean metavariables using factory
    let mut booleans = metavar_factory.list_metavariables_by_type(&SimpleType::Boolean);
    let (phi, psi, chi) = booleans
        .next_tuple()
        .ok_or_else(|| MguError::from_index_and_len(Some(SimpleType::Boolean), 2usize, 0usize))?;

    let mut dict = HashMap::new();

    // D = Detachment, a.k.a. Modus Ponens
    dict.insert("D".to_owned(), modus_ponens(phi.clone(), psi.clone(), implies_node.clone())?);

    // 1 = Simp
    dict.insert("1".to_owned(), simp(phi.clone(), psi.clone(), implies_node.clone())?);

    // 2 = Frege
    dict.insert("2".to_owned(), frege(phi.clone(), psi.clone(), chi, implies_node.clone())?);

    // 3 = Transp
    dict.insert("3".to_owned(), transp(phi, psi, not_node, implies_node)?);

    Ok(dict)
}
