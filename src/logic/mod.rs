//! Helper functions for building fundamental logic statements.
//!
//! This module provides builders for common logical axioms and rules
//! using the propositional calculus with Implies (→), Not (¬), and
//! Biimplication (↔).

pub mod polish;
pub mod propositional;

use crate::{
    Metavariable, MetavariableFactory, MguError, Node, Statement, Term, TermFactory, Type, TypeCore,
};
use itertools::Itertools;
use polish::PolishNotationEngine;
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

/// Take a string in Polish notation and return the corresponding Statement.
///
/// # Syntax
///
/// Lowercase letters correspond to the supplied Boolean variables.
/// Whitespace and control characters are ignored.
/// Semicolons (;) are used as term separators.
///
#[cfg_attr(doc, doc = include_str!("LUKASIEWICZ_NOTATION.md"))]
///
/// # Errors
///
/// Returns an error if:
/// - Variables are not Boolean type
/// - Duplicate variables or nodes are provided
/// - Unknown characters appear in the notation
/// - Stack underflow/overflow occurs during parsing
/// - No terms are specified
pub fn build_boolean_statement_from_polish<Ty, V, N, T, TF>(
    polish: &str,
    factory: &TF,
    vars: &[V],
    nodes: &[N],
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    let mut engine = PolishNotationEngine::default();
    build_boolean_statement_from_polish_with_engine(polish, factory, vars, nodes, &mut engine)
}

/// Take a string in Polish notation and return the corresponding Statement using a custom engine.
///
/// This is the internal implementation that uses a [`PolishNotationEngine`] for parsing.
/// For standard Łukasiewicz notation, use [`build_boolean_statement_from_polish`] instead.
///
/// # Errors
///
/// Returns an error if:
/// - Variables are not Boolean type
/// - Duplicate variables or nodes are provided
/// - Unknown characters appear in the notation
/// - Stack underflow/overflow occurs during parsing
/// - No terms are specified
///
/// [`PolishNotationEngine`]: `crate::logic::polish::PolishNotationEngine`
pub fn build_boolean_statement_from_polish_with_engine<Ty, V, N, T, TF>(
    polish: &str,
    factory: &TF,
    vars: &[V],
    nodes: &[N],
    engine: &mut PolishNotationEngine<V, N, T, TF>,
) -> Result<Statement<Ty, V, N, T>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    // Clear any previous state
    engine.clear_state();

    engine.setup_nodes(nodes)?;
    engine.setup_vars(vars, polish)?;
    engine.build_statement(polish, factory)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_eval::{BooleanSimpleNode, BooleanSimpleOp};
    use crate::{EnumTermFactory, SimpleType, WideMetavariableFactory};
    use strum::VariantArray;

    type TestNode = BooleanSimpleNode<SimpleType>;

    #[test]
    fn build_boolean_terms() {
        use BooleanSimpleOp::*;
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = BooleanSimpleOp::VARIANTS
            .iter()
            .cloned()
            .map(BooleanSimpleNode::from_op)
            .collect::<Vec<TestNode>>();
        let factory = EnumTermFactory::new();
        // Create a statement with hypotheses of all possible nodes in ASCII order of Łukasiewicz notation
        let test_str =
            "&pqr;+pqr;0;1;?pqr;Apq;Bpq;Cpq;Dpq;Epq;Fpq;Gpq;Hpq;Ipq;Jpq;Kpq;Lpq;Mpq;Np;Opq;Vpq;Xpq;^pqr;|pqr;1";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_ok());
        let stmt = s.unwrap();
        let a = stmt.get_assertion();
        assert_eq!(a.get_metavariable(), None);
        assert_eq!(a.get_node(), Some(TestNode::from_op(True0)));
        let ops = vec![
            And3ABC3,      // &
            Xor3ABC3,      // +
            False0,        // 0
            True0,         // 1
            IfABC3,        // ?
            OrAB2,         // A
            ImpliesBA2,    // B
            ImpliesAB2,    // C
            NotAndAB2,     // D
            BiimpAB2,      // E
            NotA2,         // F
            NotB2,         // G
            IdB2,          // H
            IdA2,          // I
            XorAB2,        // J
            AndAB2,        // K
            NotImpliesAB2, // L
            NotImpliesBA2, // M
            NotA1,         // N
            False2,        // O
            True2,         // V
            NotOrAB2,      // X
            Majority3ABC3, // ^
            Or3ABC3,       // |
        ];
        let hyps = stmt.get_hypotheses();
        assert_eq!(hyps.len(), ops.len());
        for (i, op) in ops.into_iter().enumerate() {
            assert_eq!(hyps[i].get_node(), Some(TestNode::from_op(op)));
        }
        let h = stmt.get_hypothesis(2).unwrap();
        assert_eq!(h.get_metavariable(), None);
        assert_eq!(h.get_node(), Some(TestNode::from_op(False0)));

        let h = stmt.get_hypothesis(0).unwrap();
        assert_eq!(h.get_metavariable(), None);
        assert_eq!(h.get_node(), Some(TestNode::from_op(And3ABC3)));
        assert_eq!(h.get_child(0).unwrap().get_metavariable().unwrap(), vars[0]);
        assert_eq!(h.get_child(1).unwrap().get_metavariable().unwrap(), vars[1]);
        assert_eq!(h.get_child(2).unwrap().get_metavariable().unwrap(), vars[2]);
    }

    #[test]
    fn build_boolean_std() {
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = vec![TestNode::from_op(BooleanSimpleOp::ImpliesAB2)];
        let factory = EnumTermFactory::new();
        let test_str = "p;Cpq;q";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_ok());
        let s = s.unwrap();
        assert_eq!(s.get_n_hypotheses(), 2);
    }

    #[test]
    fn build_boolean_ws_and_cntrl() {
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = vec![TestNode::from_op(BooleanSimpleOp::ImpliesAB2)];
        let factory = EnumTermFactory::new();
        let test_str = "p\u{0003};\nCpq;\t\nq ";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_ok());
        let s = s.unwrap();
        assert_eq!(s.get_n_hypotheses(), 2);
    }

    #[test]
    fn build_boolean_stack_overflow() {
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = vec![TestNode::from_op(BooleanSimpleOp::ImpliesAB2)];
        let factory = EnumTermFactory::new();
        let test_str = "Cpqr";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_err());
    }

    #[test]
    fn build_boolean_stack_underflow() {
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = vec![TestNode::from_op(BooleanSimpleOp::ImpliesAB2)];
        let factory = EnumTermFactory::new();
        let test_str = "Cp";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_err());
    }

    #[test]
    fn build_boolean_empty_string() {
        let vars = WideMetavariableFactory()
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(3)
            .collect::<Vec<_>>();
        let nodes = vec![TestNode::from_op(BooleanSimpleOp::ImpliesAB2)];
        let factory = EnumTermFactory::new();
        let test_str = "";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_err());

        let test_str = "\u{0003} \n\t";
        let s = build_boolean_statement_from_polish(test_str, &factory, &vars, &nodes);
        assert!(s.is_err());
    }
}
