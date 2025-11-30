//! Helper functions for building fundamental logic statements.
//!
//! This module provides builders for common logical axioms and rules
//! using the propositional calculus with Implies (→), Not (¬), and
//! Biimplication (↔).

pub mod propositional;

use crate::{
    Metavariable, MetavariableFactory, MguError, Node, Statement, Term, TermFactory, Type, TypeCore,
};
use itertools::Itertools;
use std::collections::HashMap;

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
    use propositional::axioms::cn_basis::{frege, simp, transp};
    use propositional::rules::cn_basis::modus_ponens;

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
