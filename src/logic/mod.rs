//! Helper functions for building fundamental logic statements.
//!
//! This module provides builders for common logical axioms and rules
//! using the propositional calculus with Implies (→), Not (¬), and
//! Biimplication (↔).

pub mod propositional;

use crate::bool_eval::BooleanSimpleOp;
use crate::{
    DistinctnessGraph, Metavariable, MetavariableFactory, MguError, Node, Statement, Term,
    TermFactory, Type, TypeCore,
};
use itertools::Itertools;
use std::collections::hash_map::Entry;
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

/// Match invisible characters and semicolon.
///
/// Used to segment hypotheses and assertion from a single string.
fn match_ws_and_semicolon(ch: char) -> bool {
    ch.is_whitespace() || ch.is_control() || ch == ';'
}

/// Apply an operator to the top of the stack.
///
/// - `ch` the code for the operation
/// - `op` the corresponding operation
/// - `factory` a factory to create new terms
/// - `node_map` a map to the nodes used by the factory
/// - `stack` a stack of Term and their Polish notation
///
/// # Errors
///
/// TODO
///
fn apply_op<Ty, V, N, T, TF>(
    ch: char,
    op: BooleanSimpleOp,
    factory: &TF,
    node_map: &HashMap<BooleanSimpleOp, N>,
    stack: &mut Vec<(T, String)>,
) -> Result<(), MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
{
    if let Some(node) = node_map.get(&op) {
        let arity = op.get_arity() as usize;
        let mut term_args = Vec::with_capacity(arity);
        let mut tree_args = Vec::with_capacity(arity);
        for i in 0..arity {
            if let Some((term, tree)) = stack.pop() {
                term_args.push(term);
                tree_args.push(tree);
            } else {
                return Err(MguError::UnificationFailure(format!(
                    "Stack underflow at '{ch}', wanted {arity} terms but found only {i}."
                )));
            }
        }
        let term = factory.create_node(node.clone(), term_args)?;
        let mut tree = ch.to_string();
        for t in tree_args.iter() {
            tree.push_str(t);
        }
        stack.push((term, tree));
    } else {
        return Err(MguError::ArgumentError(format!(
            "For '{ch}', no node supplied that maps to {op}."
        )));
    }
    Ok(())
}

/// Take a string in Polish notation and return the corresponding Statement.
///
/// Operators of arity 1 and 2 as tabulated by Prior following Bochenski and Łukasiewicz:
///
/// | Table        | Łukasiewicz | [`BooleanSimpleOp`] | Table        | Łukasiewicz | [`BooleanSimpleOp`] |
/// | ------------ | ----------- | ------------------- | ------------ | ----------- | ------------------- |
/// |              |             |                     | (0, 1)       | N           | [`NotA1`]           |
/// | (1, 1, 1, 0) | A           | [`OrAB2`]           | (0, 0, 0, 1) | X           | [`NotOrAB2`]        |
/// | (1, 1, 0, 1) | B           | [`ImpliesBA2`]      | (0, 0, 1, 0) | M           | [`NotImpliesBA2`]   |
/// | (1, 0, 1, 1) | C           | [`ImpliesAB2`]      | (0, 1, 0, 0) | L           | [`NotImpliesAB2`]   |
/// | (0, 1, 1, 1) | D           | [`NotAndAB2`]       | (1, 0, 0, 0) | K           | [`AndAB2`]          |
/// | (1, 0, 0, 1) | E           | [`BiimpAB2`]        | (0, 1, 1, 0) | J           | [`XorAB2`]          |
/// | (0, 0, 1, 1) | F           | [`NotA2`]           | (1, 1, 0, 0) | I           | [`IdA2`]            |
/// | (0, 1, 0, 1) | G           | [`NotB2`]           | (1, 0, 1, 0) | H           | [`IdB2`]            |
/// | (0, 0, 0, 0) | O           | [`False2`]          | (1, 1, 1, 1) | V           | [`True2`]           |
///
/// Operators of arity 0 and 3 novel to this function:
///
/// | Additional | [`BooleanSimpleOp`] | Additional | [`BooleanSimpleOp`] |
/// | ---------- | ------------------- | ---------- | ------------------- |
/// | 0          | [`False0`]          | 1          | [`True0`]           |
/// | &amp;      | [`And3ABC3`]        | \|         | [`Or3ABC3`]         |
/// | +          | [`Xor3ABC3`]        | ^          | [`Majority3ABC3`]   |
/// | ?          | [`IfABC3`]          | ;          | term separator      |
///
/// Lowercase letters correspond to the supplied Boolean variables.
/// Whitespace and control characters are ignored.
///
/// Adopted from:
///
/// **Prior, A. N.** (1955) *Formal Logic*, pp. 4-13.
/// Available at <https://archive.org/details/formallogic0000anpr>
///
/// # Errors
/// TODO
///
/// [`BooleanSimpleOp`]: `crate::bool_eval::BooleanSimpleOp`
/// [`NotA1`]: `crate::bool_eval::BooleanSimpleOp::NotA1`
/// [`False2`]: `crate::bool_eval::BooleanSimpleOp::False2`
/// [`NotOrAB2`]: `crate::bool_eval::BooleanSimpleOp::NotOrAB2`
/// [`NotImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesAB2`
/// [`NotB2`]: `crate::bool_eval::BooleanSimpleOp::NotB2`
/// [`NotImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::NotImpliesBA2`
/// [`NotA2`]: `crate::bool_eval::BooleanSimpleOp::NotA2`
/// [`XorAB2`]: `crate::bool_eval::BooleanSimpleOp::XorAB2`
/// [`NotAndAB2`]: `crate::bool_eval::BooleanSimpleOp::NotAndAB2`
/// [`AndAB2`]: `crate::bool_eval::BooleanSimpleOp::AndAB2`
/// [`BiimpAB2`]: `crate::bool_eval::BooleanSimpleOp::BiimpAB2`
/// [`IdA2`]: `crate::bool_eval::BooleanSimpleOp::IdA2`
/// [`ImpliesBA2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesBA2`
/// [`IdB2`]: `crate::bool_eval::BooleanSimpleOp::IdB2`
/// [`ImpliesAB2`]: `crate::bool_eval::BooleanSimpleOp::ImpliesAB2`
/// [`OrAB2`]: `crate::bool_eval::BooleanSimpleOp::OrAB2`
/// [`True2`]: `crate::bool_eval::BooleanSimpleOp::True2`
/// [`False0`]: `crate::bool_eval::BooleanSimpleOp::False0`
/// [`True0`]: `crate::bool_eval::BooleanSimpleOp::True0`
/// [`And3ABC3`]: `crate::bool_eval::BooleanSimpleOp::And3ABC3`
/// [`Or3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Or3ABC3`
/// [`Xor3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Xor3ABC3`
/// [`Majority3ABC3`]: `crate::bool_eval::BooleanSimpleOp::Majority3ABC3`
/// [`IfABC3`]: `crate::bool_eval::BooleanSimpleOp::IfABC3`
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
    let mut node_map = HashMap::with_capacity(nodes.len());
    let mut var_map = HashMap::with_capacity(vars.len());
    for n in nodes {
        if let Some(op) = n.to_boolean_op() {
            if let Some(n2) = node_map.insert(op, n.clone()) {
                return Err(MguError::ArgumentError(format!(
                    "Both {n2:?} and {n:?} map to {op:?}. Such duplicates are not allowed."
                )));
            }
        } else {
            return Err(MguError::ArgumentError(format!(
                "The node {n:?} is not associated with a BooleanSimpleOp."
            )));
        }
    }
    let mut unique_vars = Vec::with_capacity(vars.len());
    for v in vars {
        require_var_is_boolean(v)?;
        if unique_vars.contains(v) {
            return Err(MguError::ArgumentError(format!(
                "Variable {v:?} has been seen twice. Such duplicates are not allowed."
            )));
        } else {
            unique_vars.push(v.clone());
        }
    }
    unique_vars.reverse();
    for part in polish.split(match_ws_and_semicolon).rev() {
        for ch in part.chars() {
            match ch {
                '&' | '+' | '0' | '1' | '?' | 'A'..='O' | 'V' | 'X' | '^' | '|' => {
                    continue;
                }
                'a'..='z' => {
                    if let Entry::Vacant(e) = var_map.entry(ch) {
                        if let Some(var) = unique_vars.pop() {
                            e.insert(var);
                        } else {
                            return Err(MguError::ArgumentError(format!(
                "Exhausted variables while trying to accommodate '{ch}'. Already seen: {}", var_map.len()
            )));
                        }
                    }
                }
                _ => {
                    return Err(MguError::ArgumentError(format!(
                        "Unknown character in Łukasiewicz notation: '{ch}' = {ch:?}"
                    )));
                }
            }
        }
    }
    drop(unique_vars);

    let mut terms = Vec::new();
    let mut stack = Vec::new();
    for part in polish.split(match_ws_and_semicolon) {
        if part.is_empty() {
            continue;
        }
        stack.clear();
        for ch in part.chars().rev() {
            match ch {
                '&' => {
                    let op = BooleanSimpleOp::And3ABC3;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '+' => {
                    let op = BooleanSimpleOp::Xor3ABC3;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '0' => {
                    let op = BooleanSimpleOp::False0;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '1' => {
                    let op = BooleanSimpleOp::True0;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '?' => {
                    let op = BooleanSimpleOp::IfABC3;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'A' => {
                    let op = BooleanSimpleOp::OrAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'B' => {
                    let op = BooleanSimpleOp::ImpliesBA2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'C' => {
                    let op = BooleanSimpleOp::ImpliesAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'D' => {
                    let op = BooleanSimpleOp::NotAndAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'E' => {
                    let op = BooleanSimpleOp::BiimpAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'F' => {
                    let op = BooleanSimpleOp::NotA2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'G' => {
                    let op = BooleanSimpleOp::NotB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'H' => {
                    let op = BooleanSimpleOp::IdB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'I' => {
                    let op = BooleanSimpleOp::IdA2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'J' => {
                    let op = BooleanSimpleOp::XorAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'K' => {
                    let op = BooleanSimpleOp::AndAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'L' => {
                    let op = BooleanSimpleOp::NotImpliesAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'M' => {
                    let op = BooleanSimpleOp::NotImpliesBA2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'N' => {
                    let op = BooleanSimpleOp::NotA1;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'O' => {
                    let op = BooleanSimpleOp::False2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'V' => {
                    let op = BooleanSimpleOp::True2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                'X' => {
                    let op = BooleanSimpleOp::NotOrAB2;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '^' => {
                    let op = BooleanSimpleOp::Majority3ABC3;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                '|' => {
                    let op = BooleanSimpleOp::Or3ABC3;
                    apply_op(ch, op, factory, &node_map, &mut stack)?;
                }
                _ => {
                    if ch.is_ascii_lowercase() {
                        if let Some(var) = var_map.get(&ch) {
                            let var = factory.create_leaf(var.clone())?;
                            stack.push((var, ch.to_string()));
                            continue;
                        } else {
                            return Err(MguError::ArgumentError(format!(
                                "Unknown letter in Łukasiewicz notation: '{ch}' = {ch:?}"
                            )));
                        }
                    } else {
                        return Err(MguError::ArgumentError(format!(
                            "Unknown character in Łukasiewicz notation: '{ch}' = {ch:?}"
                        )));
                    }
                }
            }
        }
        let n = stack.len();
        if n != 1 {
            return Err(MguError::UnificationFailure(format!(
                "Łukasiewicz notation: '{part}' resulted in stack depth of {n}."
            )));
        }
        if let Some((term, _)) = stack.pop() {
            terms.push(term);
        }
    }
    if let Some(assertion) = terms.pop() {
        terms.shrink_to_fit();
        let s = Statement::new(assertion, terms, DistinctnessGraph::default())?;
        Ok(s)
    } else {
        Err(MguError::ArgumentError("No terms specified.".to_string()))
    }
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
    use crate::bool_eval::BooleanSimpleNode;
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
