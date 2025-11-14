//! Helper functions for building fundamental logic statements.
//!
//! This module provides builders for common logical axioms and rules
//! using the propositional calculus with Implies (→), Not (¬), and
//! Biimplication (↔).

use crate::{
    DistinctnessGraph, Metavariable, MetavariableFactory, MguError, Node, Statement, Term,
    TermFactory, Type, TypeCore,
};
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

/// Gating function.
///
/// # Errors
/// - if the variable isn't of type Boolean
/// - if the variable's type doesn't support Booleans.
pub fn require_var_is_boolean<V: Metavariable>(some_var: &V) -> Result<(), MguError> {
    let some_type = some_var.get_type()?;
    if !some_type.is_boolean() {
        let wanted = <V::Type>::try_boolean().ok();
        if let Some(bool_type) = wanted {
            return Err(MguError::from_found_and_expected_types(
                false, &some_type, &bool_type,
            ));
        } else {
            return Err(MguError::TypeCapabilityUnsupported {
                capability: "Boolean",
            });
        }
    }
    Ok(())
}

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
/// use symbolic_mgu::{EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, Metavariable, NodeByte, SimpleType};
/// use itertools::Itertools;
///
/// // Create factory for building terms
/// let factory = EnumTermFactory::new();
///
/// let vars = MetaByteFactory();
/// let (phi, psi) = vars.list_metavariables_by_type(&SimpleType::Boolean).tuples().next().unwrap();
///
/// // Create Simp axiom: ((φ → (ψ → φ)); ∅; ∅)
/// let axiom = simp(&factory, phi, psi, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0); // It's an axiom
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn simp<Ty, V, N, T, TF>(
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
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;

    // Build (ψ → φ)
    let psi_implies_phi = factory.create_node(implies_node.clone(), vec![psi, phi.clone()])?;

    // Build (φ → (ψ → φ))
    let assertion = factory.create_node(implies_node, vec![phi, psi_implies_phi])?;

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
/// use symbolic_mgu::{EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, Metavariable, NodeByte, SimpleType};
/// use itertools::Itertools;
///
/// // Create factory for building terms
/// let factory = EnumTermFactory::new();
///
/// let vars = MetaByteFactory();
/// let (phi, psi, chi) = vars.list_metavariables_by_type(&SimpleType::Boolean).tuples().next().unwrap();
///
/// // Create Frege axiom (distributivity)
/// let axiom = frege(&factory, phi, psi, chi, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn frege<Ty, V, N, T, TF>(
    factory: &TF,
    phi_var: V,
    psi_var: V,
    chi_var: V,
    implies_node: N,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Verify all variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;
    require_var_is_boolean(&chi_var)?;

    // Build terms for φ, ψ, χ
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;
    let chi = factory.create_leaf(chi_var)?;

    // Build (ψ → χ)
    let psi_implies_chi =
        factory.create_node(implies_node.clone(), vec![psi.clone(), chi.clone()])?;

    // Build (φ → (ψ → χ))
    let phi_implies_psi_implies_chi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), psi_implies_chi])?;

    // Build (φ → ψ)
    let phi_implies_psi = factory.create_node(implies_node.clone(), vec![phi.clone(), psi])?;

    // Build (φ → χ)
    let phi_implies_chi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), chi.clone()])?;

    // Build ((φ → ψ) → (φ → χ))
    let right_side =
        factory.create_node(implies_node.clone(), vec![phi_implies_psi, phi_implies_chi])?;

    // Build ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
    let assertion =
        factory.create_node(implies_node, vec![phi_implies_psi_implies_chi, right_side])?;

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
/// use symbolic_mgu::{EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, Metavariable, NodeByte, SimpleType};
/// use itertools::Itertools;
///
/// // Create factory for building terms
/// let factory = EnumTermFactory::new();
///
/// let vars = MetaByteFactory();
/// let (phi, psi) = vars.list_metavariables_by_type(&SimpleType::Boolean).tuples().next().unwrap();
///
/// // Create Transp axiom (contrapositive)
/// let axiom = transp(&factory, phi, psi, NodeByte::Not, NodeByte::Implies).unwrap();
///
/// assert_eq!(axiom.get_n_hypotheses(), 0);
/// ```
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn transp<Ty, V, N, T, TF>(
    factory: &TF,
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

    // Build ¬φ
    let not_phi = factory.create_node(not_node.clone(), vec![phi.clone()])?;

    // Build ¬ψ
    let not_psi = factory.create_node(not_node, vec![psi.clone()])?;

    // Build (¬φ → ¬ψ)
    let not_phi_implies_not_psi =
        factory.create_node(implies_node.clone(), vec![not_phi, not_psi])?;

    // Build (ψ → φ)
    let psi_implies_phi = factory.create_node(implies_node.clone(), vec![psi, phi])?;

    // Build ((¬φ → ¬ψ) → (ψ → φ))
    let assertion =
        factory.create_node(implies_node, vec![not_phi_implies_not_psi, psi_implies_phi])?;

    Statement::simple_axiom(assertion)
}

/// Type alias for statement dictionaries used in compact proof parsing.
pub type Dictionary<Ty, V, N, T> = HashMap<String, Statement<Ty, V, N, T>>;

/// Build standard statement dictionary for compact proofs.
///
/// Returns a `HashMap` mapping:
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
/// ```
/// use symbolic_mgu::logic::create_dict;
/// use symbolic_mgu::{EnumTermFactory, MetaByteFactory, NodeByte, SimpleType};
///
/// // Create factories
/// let term_factory = EnumTermFactory::new();
/// let metavar_factory = MetaByteFactory();
///
/// let dict = create_dict(&term_factory, &metavar_factory, NodeByte::Implies, NodeByte::Not).unwrap();
///
/// assert!(dict.contains_key("D"));  // Modus Ponens
/// assert!(dict.contains_key("1"));  // Simp
/// assert!(dict.contains_key("2"));  // Frege
/// assert!(dict.contains_key("3"));  // Transp
/// ```
///
/// # Errors
///
/// Returns an error if statement construction fails or if there are insufficient
/// metavariables of Boolean type available.
pub fn create_dict<TF, MF, Ty, V, N, T>(
    term_factory: &TF,
    metavar_factory: &MF,
    implies_node: N,
    not_node: N,
) -> Result<Dictionary<Ty, V, N, T>, MguError>
where
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermNode = N, TermMetavariable = V>,
    MF: MetavariableFactory<MetavariableType = Ty, Metavariable = V>,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    Ty: Type,
{
    // Get three Boolean metavariables using factory
    let our_bool = Ty::try_boolean()?;
    let mut booleans = metavar_factory.list_metavariables_by_type(&our_bool);
    let (phi, psi, chi) = booleans
        .next_tuple()
        .ok_or_else(|| MguError::from_type_index_and_len(our_bool.clone(), 2usize, 0usize))?;

    let mut dict = HashMap::new();

    // D = Detachment, a.k.a. Modus Ponens
    dict.insert(
        "D".to_owned(),
        modus_ponens(term_factory, phi.clone(), psi.clone(), implies_node.clone())?,
    );

    // 1 = Simp
    dict.insert(
        "1".to_owned(),
        simp(term_factory, phi.clone(), psi.clone(), implies_node.clone())?,
    );

    // 2 = Frege
    dict.insert(
        "2".to_owned(),
        frege(
            term_factory,
            phi.clone(),
            psi.clone(),
            chi,
            implies_node.clone(),
        )?,
    );

    // 3 = Transp
    dict.insert(
        "3".to_owned(),
        transp(term_factory, phi, psi, not_node, implies_node)?,
    );

    Ok(dict)
}
