//! Axioms of Propositional Calculus in the C-N basis.
//!
//! "C" here refers to material implication and "N" to the not operator.
//!
//! As tabulated by Prior following Bochenski and Łukasiewicz:
//!
//! | Table        | Łukasiewicz | [`BooleanSimpleOp`] | Table        | Łukasiewicz | [`BooleanSimpleOp`] |
//! | ------------ | ----------- | ------------------- | ------------ | ----------- | ------------------- |
//! | (1, 0)       |             | [`IdA1`]            | (0, 1)       | N           | [`NotA1`]           |
//! | (1, 1, 1, 0) | A           | [`OrAB2`]           | (0, 0, 0, 1) | X           | [`NotOrAB2`]        |
//! | (1, 1, 0, 1) | B           | [`ImpliesBA2`]      | (0, 0, 1, 0) | M           | [`NotImpliesBA2`]   |
//! | (1, 0, 1, 1) | C           | [`ImpliesAB2`]      | (0, 1, 0, 0) | L           | [`NotImpliesAB2`]   |
//! | (0, 1, 1, 1) | D           | [`NotAndAB2`]       | (1, 0, 0, 0) | K           | [`AndAB2`]          |
//! | (1, 0, 0, 1) | E           | [`BiimpAB2`]        | (0, 1, 1, 0) | J           | [`XorAB2`]          |
//! | (0, 0, 1, 1) | F           | [`NotA2`]           | (1, 1, 0, 0) | I           | [`IdA2`]            |
//! | (0, 1, 0, 1) | G           | [`NotB2`]           | (1, 0, 1, 0) | H           | [`IdB2`]            |
//! | (0, 0, 0, 0) | O           | [`False2`]          | (1, 1, 1, 1) | V           | [`True2`]           |
//!
//! - Metamath standard following Łukasiewicz: [`simp()`], [`frege()`], and [`transp()`].
//! - Frege's system (1879): [`simp()`], [`frege()`], [`pm2_04()`], [`pm2_16()`], [`pm2_12()`], and [`pm2_14()`].
//! - Łukasiewicz's Standard C-N System (1929): [`pm2_06()`], [`pm2_18()`], and [`pm2_24()`]
//! - Meredith's Single-Axiom C-N System (1953): [`meredith_cn()`]
//!
//!
//! Adopted from:
//!
//! **Prior, A. N.** (1955) *Formal Logic*, pp. 4-13, 301-303.
//! Available at <https://archive.org/details/formallogic0000anpr>
//!
//! [`BooleanSimpleOp`]: `crate::bool_eval::BooleanSimpleOp`
//! [`IdA1`]: `crate::bool_eval::BooleanSimpleOp::IdA1`
//! [`NotA1`]: `crate::bool_eval::BooleanSimpleOp::NotA1`
//! [`False2`]: `crate::bool_eval::BooleanSimpleOp::False2`
//! [`NotOrAB2`]: `crate::bool_eval::BooleanSimpleOp::NotOrAB2`
//! [`NotImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesAB2`
//! [`NotB2`]: `crate::bool_eval::BooleanSimpleOp::NotB2`
//! [`NotImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesBA2`
//! [`NotA2`]: `crate::bool_eval::BooleanSimpleOp::NotA2`
//! [`XorAB2`]: `crate::bool_eval::BooleanSimpleOp::XorAB2`
//! [`NotAndAB2`]: `crate::bool_eval::BooleanSimpleOp::NotAndAB2`
//! [`AndAB2`]: `crate::bool_eval::BooleanSimpleOp::AndAB2`
//! [`BiimpAB2`]: `crate::bool_eval::BooleanSimpleOp::BiimpAB2`
//! [`IdA2`]: `crate::bool_eval::BooleanSimpleOp::IdA2`
//! [`ImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesBA2`
//! [`IdB2`]: `crate::bool_eval::BooleanSimpleOp::IdB2`
//! [`ImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesAB2`
//! [`OrAB2`]: `crate::bool_eval::BooleanSimpleOp::OrAB2`
//! [`True2`]: `crate::bool_eval::BooleanSimpleOp::True2`

use crate::logic::require_var_is_boolean;
use crate::{Metavariable, MguError, Node, Statement, Term, TermFactory, Type};

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
/// use symbolic_mgu::logic::propositional::axioms::cn_basis::simp;
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
/// use symbolic_mgu::logic::propositional::axioms::cn_basis::frege;
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
/// use symbolic_mgu::logic::propositional::axioms::cn_basis::transp;
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

/// Build the axiom: ((𝜑 → (𝜓 → 𝜒)) → (𝜓 → (𝜑 → 𝜒)))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_04<Ty, V, N, T, TF>(
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
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;
    require_var_is_boolean(&chi_var)?;

    // Build terms for φ, ψ, and 𝜒
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;
    let chi = factory.create_leaf(chi_var)?;

    // Build (𝜓 → 𝜒)
    let psi_implies_chi =
        factory.create_node(implies_node.clone(), vec![psi.clone(), chi.clone()])?;

    // Build (𝜑 → (𝜓 → 𝜒))
    let phi_implies_psi_implies_chi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), psi_implies_chi])?;

    // Build (𝜑 → 𝜒)
    let phi_implies_chi = factory.create_node(implies_node.clone(), vec![phi.clone(), chi])?;

    // Build (𝜓 → (𝜑 → 𝜒))
    let psi_implies_phi_implies_chi =
        factory.create_node(implies_node.clone(), vec![psi.clone(), phi_implies_chi])?;

    // Build ((𝜑 → (𝜓 → 𝜒)) → (𝜓 → (𝜑 → 𝜒)))
    let assertion = factory.create_node(
        implies_node,
        vec![phi_implies_psi_implies_chi, psi_implies_phi_implies_chi],
    )?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: ((𝜑 → 𝜓) → ((𝜓 → 𝜒) → (𝜑 → 𝜒)))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_06<Ty, V, N, T, TF>(
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
    // Verify both variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;
    require_var_is_boolean(&chi_var)?;

    // Build terms for φ, ψ, and 𝜒
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;
    let chi = factory.create_leaf(chi_var)?;

    // Build (𝜑 → 𝜓)
    let phi_implies_psi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), psi.clone()])?;

    // Build (𝜓 → 𝜒)
    let psi_implies_chi = factory.create_node(implies_node.clone(), vec![psi, chi.clone()])?;

    // Build (𝜑 → 𝜒)
    let phi_implies_chi = factory.create_node(implies_node.clone(), vec![phi, chi])?;

    // Build ((𝜓 → 𝜒) → (𝜑 → 𝜒))
    let psi_implies_chi_implies_phi_implies_chi =
        factory.create_node(implies_node.clone(), vec![psi_implies_chi, phi_implies_chi])?;

    // Build ((𝜑 → 𝜓) → ((𝜓 → 𝜒) → (𝜑 → 𝜒)))
    let assertion = factory.create_node(
        implies_node,
        vec![phi_implies_psi, psi_implies_chi_implies_phi_implies_chi],
    )?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: (𝜑 → ¬ ¬ 𝜑)
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_12<Ty, V, N, T, TF>(
    factory: &TF,
    phi_var: V,
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
    // Verify variable Boolean
    require_var_is_boolean(&phi_var)?;

    // Build term for φ
    let phi = factory.create_leaf(phi_var)?;

    // Build ¬φ
    let not_phi = factory.create_node(not_node.clone(), vec![phi.clone()])?;

    // Build ¬¬φ
    let not_not_phi = factory.create_node(not_node.clone(), vec![not_phi])?;

    // Build (𝜑 → ¬ ¬ 𝜑)
    let assertion = factory.create_node(implies_node, vec![phi, not_not_phi])?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: (¬ ¬ 𝜑 → 𝜑)
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_14<Ty, V, N, T, TF>(
    factory: &TF,
    phi_var: V,
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
    // Verify variable is Boolean
    require_var_is_boolean(&phi_var)?;

    // Build term for φ
    let phi = factory.create_leaf(phi_var)?;

    // Build ¬φ
    let not_phi = factory.create_node(not_node.clone(), vec![phi.clone()])?;

    // Build ¬¬φ
    let not_not_phi = factory.create_node(not_node.clone(), vec![not_phi])?;

    // Build (¬ ¬ 𝜑 → 𝜑)
    let assertion = factory.create_node(implies_node, vec![not_not_phi, phi])?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: ((𝜑 → 𝜓) → (¬ 𝜓 → ¬ 𝜑))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_16<Ty, V, N, T, TF>(
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

    // Build ¬ψ
    let not_psi = factory.create_node(not_node.clone(), vec![psi.clone()])?;

    // Build ¬φ
    let not_phi = factory.create_node(not_node, vec![phi.clone()])?;

    // Build (¬ 𝜓 → ¬ 𝜑)
    let not_psi_implies_not_phi =
        factory.create_node(implies_node.clone(), vec![not_psi, not_phi])?;

    // Build (𝜑 → 𝜓)
    let phi_implies_psi = factory.create_node(implies_node.clone(), vec![phi, psi])?;

    // Build ((𝜑 → 𝜓) → (¬ 𝜓 → ¬ 𝜑))
    let assertion =
        factory.create_node(implies_node, vec![phi_implies_psi, not_psi_implies_not_phi])?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: ((¬ 𝜑 → 𝜑) → 𝜑)
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_18<Ty, V, N, T, TF>(
    factory: &TF,
    phi_var: V,
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
    // Verify variable is Boolean
    require_var_is_boolean(&phi_var)?;

    // Build term for φ
    let phi = factory.create_leaf(phi_var)?;

    // Build ¬φ
    let not_phi = factory.create_node(not_node, vec![phi.clone()])?;

    // Build (¬ 𝜑 → 𝜓)
    let not_phi_implies_phi =
        factory.create_node(implies_node.clone(), vec![not_phi, phi.clone()])?;

    // Build ((¬ 𝜑 → 𝜑) → 𝜑)
    let assertion = factory.create_node(implies_node, vec![not_phi_implies_phi, phi])?;

    Statement::simple_axiom(assertion)
}

/// Build the axiom: (𝜑 → (¬ 𝜑 → 𝜓))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
pub fn pm2_24<Ty, V, N, T, TF>(
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
    let not_phi = factory.create_node(not_node, vec![phi.clone()])?;

    // Build (¬ 𝜑 → 𝜓)
    let not_phi_implies_psi = factory.create_node(implies_node.clone(), vec![not_phi, psi])?;

    // Build (𝜑 → (¬ 𝜑 → 𝜓))
    let assertion = factory.create_node(implies_node, vec![phi, not_phi_implies_psi])?;

    Statement::simple_axiom(assertion)
}

/// Build the Axiom: (((((𝜑 → 𝜓) → (¬ 𝜒 → ¬ 𝜃)) → 𝜒) → 𝜏) → ((𝜏 → 𝜑) → (𝜃 → 𝜑)))
///
/// # Errors
///
/// Returns an error if term construction or statement validation fails.
#[allow(clippy::too_many_arguments)]
pub fn meredith_cn<Ty, V, N, T, TF>(
    factory: &TF,
    phi_var: V,
    psi_var: V,
    chi_var: V,
    theta_var: V,
    tau_var: V,
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
    // Verify all variables are Boolean
    require_var_is_boolean(&phi_var)?;
    require_var_is_boolean(&psi_var)?;
    require_var_is_boolean(&chi_var)?;
    require_var_is_boolean(&theta_var)?;
    require_var_is_boolean(&tau_var)?;

    // Build terms for 𝜑, 𝜓, 𝜒, 𝜃, and 𝜏
    let phi = factory.create_leaf(phi_var)?;
    let psi = factory.create_leaf(psi_var)?;
    let chi = factory.create_leaf(chi_var)?;
    let theta = factory.create_leaf(theta_var)?;
    let tau = factory.create_leaf(tau_var)?;

    // Build (𝜑 → 𝜓)
    let phi_implies_psi =
        factory.create_node(implies_node.clone(), vec![phi.clone(), psi.clone()])?;

    // Build ¬ 𝜒
    let not_chi = factory.create_node(not_node.clone(), vec![chi.clone()])?;

    // Build ¬ 𝜃
    let not_theta = factory.create_node(not_node.clone(), vec![theta.clone()])?;

    // Build (¬ 𝜒 → ¬ 𝜃)
    let theta_implies_chi = factory.create_node(implies_node.clone(), vec![not_chi, not_theta])?;

    // Build ((𝜑 → 𝜓) → (¬ 𝜒 → ¬ 𝜃))
    let left = factory.create_node(
        implies_node.clone(),
        vec![phi_implies_psi, theta_implies_chi],
    )?;

    // Build (((𝜑 → 𝜓) → (¬ 𝜒 → ¬ 𝜃)) → 𝜒)
    let left = factory.create_node(implies_node.clone(), vec![left, chi])?;

    // Build ((((𝜑 → 𝜓) → (¬ 𝜒 → ¬ 𝜃)) → 𝜒) → 𝜏)
    let left = factory.create_node(implies_node.clone(), vec![left, tau.clone()])?;

    // Build (𝜏 → 𝜑)
    let tau_implies_phi = factory.create_node(implies_node.clone(), vec![tau, phi.clone()])?;

    // Build (𝜃 → 𝜑)
    let theta_implies_phi = factory.create_node(implies_node.clone(), vec![theta, phi])?;

    // Build ((𝜏 → 𝜑) → (𝜃 → 𝜑))
    let right = factory.create_node(
        implies_node.clone(),
        vec![tau_implies_phi, theta_implies_phi],
    )?;

    // Build (((((𝜑 → 𝜓) → (¬ 𝜒 → ¬ 𝜃)) → 𝜒) → 𝜏) → ((𝜏 → 𝜑) → (𝜃 → 𝜑)))
    let assertion = factory.create_node(implies_node, vec![left, right])?;

    Statement::simple_axiom(assertion)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_eval::BooleanSimpleOp::{ImpliesAB2, NotA1};
    use crate::bool_eval::{test_tautology, BooleanSimpleNode};
    use crate::{EnumTermFactory, MetavariableFactory, SimpleType, WideMetavariableFactory};
    use itertools::Itertools;

    type MyType = SimpleType;
    type MyNode = BooleanSimpleNode<MyType>;

    #[test]
    fn simp_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = simp(&factory, phi, psi, MyNode::from_op(ImpliesAB2));
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn frege_tautology() {
        let (phi, psi, chi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = frege(&factory, phi, psi, chi, MyNode::from_op(ImpliesAB2));
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn transp_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = transp(
            &factory,
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
    fn pm2_04_tautology() {
        let (phi, psi, chi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_04(&factory, phi, psi, chi, MyNode::from_op(ImpliesAB2));
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn pm2_06_tautology() {
        let (phi, psi, chi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_06(&factory, phi, psi, chi, MyNode::from_op(ImpliesAB2));
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn pm2_12_tautology() {
        let phi = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_12(
            &factory,
            phi,
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn pm2_14_tautology() {
        let phi = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_14(
            &factory,
            phi,
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn pm2_16_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_16(
            &factory,
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
    fn pm2_18_tautology() {
        let phi = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_18(
            &factory,
            phi,
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    #[test]
    fn pm2_24_tautology() {
        let (phi, psi) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = pm2_24(
            &factory,
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
    fn meredith_cn_tautology() {
        let (phi, psi, chi, theta, tau) = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let factory = EnumTermFactory::new();
        let statement = meredith_cn(
            &factory,
            phi,
            psi,
            chi,
            theta,
            tau,
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        );
        assert!(statement.is_ok());
        let statement = statement.unwrap();
        assert_eq!(test_tautology(statement.get_assertion()), Ok(true));
    }

    // Tests comparing axiom builders with Polish notation builder

    use crate::logic::build_boolean_statement_from_polish;

    #[test]
    fn simp_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = simp(&factory, vars[0], vars[1], MyNode::from_op(ImpliesAB2)).unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CpCqp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn frege_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(3)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = frege(
            &factory,
            vars[0],
            vars[1],
            vars[2],
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCpCqrCCpqCpr",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn transp_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = transp(
            &factory,
            vars[0],
            vars[1],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCNpNqCqp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_04_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(3)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_04(
            &factory,
            vars[0],
            vars[1],
            vars[2],
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCpCqrCqCpr",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_06_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(3)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_06(
            &factory,
            vars[0],
            vars[1],
            vars[2],
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCpqCCqrCpr",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_12_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(1)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_12(
            &factory,
            vars[0],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CpNNp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_14_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(1)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_14(
            &factory,
            vars[0],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CNNpp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_16_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_16(
            &factory,
            vars[0],
            vars[1],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCpqCNqNp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_18_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(1)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_18(
            &factory,
            vars[0],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCNppp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn pm2_24_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(2)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = pm2_24(
            &factory,
            vars[0],
            vars[1],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CpCNpq",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }

    #[test]
    fn meredith_cn_equals_polish() {
        let vars = WideMetavariableFactory::new()
            .list_metavariables_by_type(&MyType::Boolean)
            .take(5)
            .collect::<Vec<_>>();
        let factory = EnumTermFactory::new();

        let from_builder = meredith_cn(
            &factory,
            vars[0],
            vars[1],
            vars[2],
            vars[3],
            vars[4],
            MyNode::from_op(NotA1),
            MyNode::from_op(ImpliesAB2),
        )
        .unwrap();

        let from_polish = build_boolean_statement_from_polish(
            "CCCCCpqCNrNsrtCCtpCsp",
            &factory,
            &vars,
            &[MyNode::from_op(ImpliesAB2), MyNode::from_op(NotA1)],
        )
        .unwrap();

        assert_eq!(from_builder.get_assertion(), from_polish.get_assertion());
        assert_eq!(
            from_builder.get_n_hypotheses(),
            from_polish.get_n_hypotheses()
        );
    }
}
