//! Polish notation support for Boolean statements.
//!
//! This module provides support for parsing Boolean statements written in
//! Polish notation, including Łukasiewicz notation following the conventions
//! of Prior (1955) and earlier logicians.

use crate::bool_eval::BooleanSimpleOp;
use crate::{
    DistinctnessGraph, Metavariable, MguError, Node, Statement, Term, TermFactory, Type,
    TypeFactory,
};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::marker::PhantomData;

/// Polish notation parsing engine.
///
/// Holds the operator mapping and internal state for parsing Polish notation expressions.
/// The Default implementation provides standard Łukasiewicz notation mappings.
///
/// Lowercase ASCII letters ('a'-'z') are reserved for variables and cannot be mapped to operators.
/// Whitespace, control characters, and semicolons are reserved as separators and cannot be mapped.
///
/// # Type Parameters
///
/// - `V`: [`Metavariable`] type
/// - `N`: [`Node`] type
/// - `T`: [`Term`] type
/// - `TF`: [`TermFactory`] type
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::polish::PolishNotationEngine;
/// use symbolic_mgu::bool_eval::BooleanSimpleOp;
///
/// type V = ();
/// type N = ();
/// type T = ();
/// type TF = ();
/// type TyF = ();
///
/// // Use standard Łukasiewicz mappings
/// let engine: PolishNotationEngine<V, N, T, TF, TyF> = PolishNotationEngine::default();
/// assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));
/// assert_eq!(engine.get_operator('N'), Some(&BooleanSimpleOp::NotA1));
/// ```
///
/// [`Metavariable`]: `crate::Metavariable`
/// [`Node`]: `crate::Node`
/// [`Term`]: `crate::Term`
/// [`TermFactory`]: `crate::TermFactory`
#[derive(Debug)]
pub struct PolishNotationEngine<V, N, T, TF, TyF> {
    /// Mapping from characters to Boolean operators
    operator_map: HashMap<char, BooleanSimpleOp>,
    /// Mapping from Boolean operators to nodes (populated during parsing)
    node_map: HashMap<BooleanSimpleOp, N>,
    /// Mapping from characters to variables (populated during parsing)
    var_map: HashMap<char, V>,
    /// Working stack for parsing (cleared between terms)
    stack: Vec<(T, String)>,
    /// Phantom data to maintain type parameter `TF` in the struct signature.
    unused: PhantomData<TF>,
    /// Phantom data to maintain type parameter `TyF` in the struct signature.
    unused2: PhantomData<TyF>,
}

impl<V, N, T, TF, TyF> PolishNotationEngine<V, N, T, TF, TyF> {
    /// Creates a new empty Polish notation engine.
    ///
    /// Use this constructor when you want to define a custom operator mapping.
    /// For standard (and our extension to) Łukasiewicz notation, use `PolishNotationEngine::default()` instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::polish::PolishNotationEngine;
    /// use symbolic_mgu::bool_eval::BooleanSimpleOp;
    ///
    /// type V = ();
    /// type N = ();
    /// type T = ();
    /// type TF = ();
    /// type TyF = ();
    ///
    /// let mut engine: PolishNotationEngine<V, N, T, TF, TyF> = PolishNotationEngine::new();
    /// assert_eq!(engine.get_operator('C'), None);
    ///
    /// engine.insert_operator('C', BooleanSimpleOp::ImpliesAB2).unwrap();
    /// assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            operator_map: HashMap::new(),
            node_map: HashMap::new(),
            var_map: HashMap::new(),
            stack: Vec::new(),
            unused: PhantomData,
            unused2: PhantomData,
        }
    }

    /// Inserts a character-to-operator mapping.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The character is a lowercase ASCII letter ('a'-'z')
    /// - The character is whitespace, a control character, or semicolon
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::polish::PolishNotationEngine;
    /// use symbolic_mgu::bool_eval::BooleanSimpleOp;
    ///
    /// type V = ();
    /// type N = ();
    /// type T = ();
    /// type TF = ();
    /// type TyF = ();
    ///
    /// let mut engine: PolishNotationEngine<V, N, T, TF, TyF> = PolishNotationEngine::new();
    ///
    /// // Valid insertion
    /// assert!(engine.insert_operator('C', BooleanSimpleOp::ImpliesAB2).is_ok());
    ///
    /// // Invalid - lowercase reserved for variables
    /// assert!(engine.insert_operator('c', BooleanSimpleOp::ImpliesAB2).is_err());
    ///
    /// // Invalid - whitespace reserved as separator
    /// assert!(engine.insert_operator(' ', BooleanSimpleOp::ImpliesAB2).is_err());
    /// ```
    pub fn insert_operator(&mut self, ch: char, op: BooleanSimpleOp) -> Result<(), MguError> {
        if ch.is_ascii_lowercase() {
            return Err(MguError::ArgumentError(format!(
                "Cannot map lowercase ASCII character '{ch}' to operator - reserved for variables"
            )));
        }
        if is_separator(ch) {
            return Err(MguError::ArgumentError(format!(
                "Cannot map separator character '{ch}' to operator - reserved as separator"
            )));
        }
        self.operator_map.insert(ch, op);
        Ok(())
    }

    /// Gets the operator associated with a character.
    ///
    /// Returns `None` if the character has no mapping.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::polish::PolishNotationEngine;
    /// use symbolic_mgu::bool_eval::BooleanSimpleOp;
    ///
    /// type V = ();
    /// type N = ();
    /// type T = ();
    /// type TF = ();
    /// type TyF = ();
    ///
    /// let engine: PolishNotationEngine<V, N, T, TF, TyF> = PolishNotationEngine::default();
    /// assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));
    /// assert_eq!(engine.get_operator('z'), None); // Variables have no mapping
    /// ```
    #[must_use]
    pub fn get_operator(&self, ch: char) -> Option<&BooleanSimpleOp> {
        self.operator_map.get(&ch)
    }

    /// Clears the internal parsing state.
    ///
    /// This clears the node map, variable map, and stack, but preserves
    /// the operator mapping configuration.
    pub(crate) fn clear_state(&mut self) {
        self.node_map.clear();
        self.var_map.clear();
        self.stack.clear();
    }

    /// Gets a reference to the node map.
    pub(crate) fn node_map(&self) -> &HashMap<BooleanSimpleOp, N> {
        &self.node_map
    }

    /// Gets a mutable reference to the node map.
    pub(crate) fn node_map_mut(&mut self) -> &mut HashMap<BooleanSimpleOp, N> {
        &mut self.node_map
    }

    /// Gets a reference to the variable map.
    pub(crate) fn var_map(&self) -> &HashMap<char, V> {
        &self.var_map
    }

    /// Gets a mutable reference to the variable map.
    pub(crate) fn var_map_mut(&mut self) -> &mut HashMap<char, V> {
        &mut self.var_map
    }

    /// Gets a reference to the stack.
    pub(crate) fn stack(&self) -> &Vec<(T, String)> {
        &self.stack
    }

    /// Gets a mutable reference to the stack.
    pub(crate) fn stack_mut(&mut self) -> &mut Vec<(T, String)> {
        &mut self.stack
    }
}

impl<Ty, V, N, T, TF, TyF> PolishNotationEngine<V, N, T, TF, TyF>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
    TyF: TypeFactory<Type = Ty>,
{
    /// Populate `node_map` prior to building terms or statements.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Duplicate nodes are provided
    /// - Any of the provided nodes does not map to [`BooleanSimpleOp`] via [`to_boolean_op()`].
    ///
    /// [`BooleanSimpleOp`]: `crate::bool_eval::BooleanSimpleOp`
    /// [`to_boolean_op()`]: `crate::Node::to_boolean_op()`
    pub fn setup_nodes(&mut self, nodes: &[N]) -> Result<(), MguError> {
        let node_map = self.node_map_mut();
        node_map.reserve(nodes.len());
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
        Ok(())
    }

    /// Populate `var_map` prior to building terms or statements.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Variables are not Boolean type
    /// - Duplicate variables are provided
    /// - Unknown characters appear in the notation
    pub fn setup_vars(
        &mut self,
        type_factory: &TyF,
        vars: &[V],
        polish: &str,
    ) -> Result<(), MguError>
    where
        TyF: TypeFactory<Type = V::Type>,
    {
        // Validate and prepare potential variables
        let mut unique_vars = Vec::with_capacity(vars.len());
        for v in vars {
            super::require_var_is_boolean(type_factory, v)?;
            if unique_vars.contains(v) {
                return Err(MguError::ArgumentError(format!(
                    "Variable {v:?} has been seen twice. Such duplicates are not allowed."
                )));
            } else {
                unique_vars.push(v.clone());
            }
        }
        unique_vars.reverse();

        // First pass: identify all variables used in the notation
        for part in polish.split(is_separator).rev() {
            for ch in part.chars() {
                if let Some(_op) = self.get_operator(ch) {
                    // Valid operator, continue
                    continue;
                } else if ch.is_ascii_lowercase() {
                    // Variable character
                    let var_map = self.var_map_mut();
                    if let Entry::Vacant(e) = var_map.entry(ch) {
                        if let Some(var) = unique_vars.pop() {
                            e.insert(var);
                        } else {
                            return Err(MguError::ArgumentError(format!(
                            "Exhausted variables while trying to accommodate '{ch}'. Already seen: {}",
                            var_map.len()
                        )));
                        }
                    }
                } else {
                    return Err(MguError::ArgumentError(format!(
                        "Unknown character in Polish notation: '{ch}' = {ch:?}"
                    )));
                }
            }
        }
        Ok(())
    }

    /// Build a term from Polish notation after nodes and vars have been setup.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Unknown characters appear in the notation
    /// - Stack underflow/overflow occurs during parsing
    pub fn build_term(&mut self, single_part: &str, factory: &TF) -> Result<T, MguError> {
        self.stack_mut().clear();

        for ch in single_part.chars().rev() {
            if let Some(&op) = self.get_operator(ch) {
                // Apply operator - need to clone `node_map` to avoid borrow conflicts
                let node = self
                    .node_map()
                    .get(&op)
                    .ok_or_else(|| {
                        MguError::ArgumentError(format!(
                            "For '{ch}', no node supplied that maps to {op}."
                        ))
                    })?
                    .clone();

                let arity = op.get_arity() as usize;
                let mut term_args = Vec::with_capacity(arity);
                let mut tree_args = Vec::with_capacity(arity);
                let stack = self.stack_mut();
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
                let term = factory.create_node(node, term_args)?;
                let mut tree = ch.to_string();
                for t in tree_args.iter() {
                    tree.push_str(t);
                }
                self.stack_mut().push((term, tree));
            } else if ch.is_ascii_lowercase() {
                // Variable
                let var = self
                    .var_map()
                    .get(&ch)
                    .ok_or_else(|| {
                        MguError::ArgumentError(format!(
                            "Unknown letter in Polish notation: '{ch}' = {ch:?}"
                        ))
                    })?
                    .clone();
                let var = factory.create_leaf(var)?;
                self.stack_mut().push((var, ch.to_string()));
            } else {
                return Err(MguError::ArgumentError(format!(
                    "Unknown character in Polish notation: '{ch}' = {ch:?}"
                )));
            }
        }

        let n = self.stack().len();

        if let Some((term, _)) = self.stack_mut().pop() {
            if n == 1 {
                return Ok(term);
            }
        }
        Err(MguError::UnificationFailure(format!(
            "Polish notation: '{single_part}' resulted in stack depth of {n}."
        )))
    }

    /// Build a statement from Polish notation after nodes and vars have been setup.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Unknown characters appear in the notation
    /// - Stack underflow/overflow occurs during parsing
    /// - No terms are specified
    pub fn build_statement(
        &mut self,
        polish: &str,
        factory: &TF,
    ) -> Result<Statement<Ty, V, N, T>, MguError>
    where
        TF: TermFactory<T, Ty, V, N, TyF>,
        TyF: TypeFactory<Type = Ty>,
    {
        let mut terms = Vec::new();

        for part in polish.split(is_separator) {
            if part.is_empty() {
                continue;
            }
            terms.push(self.build_term(part, factory)?);
        }

        if let Some(assertion) = terms.pop() {
            terms.shrink_to_fit();
            let s = Statement::new(
                factory.type_factory(),
                assertion,
                terms,
                DistinctnessGraph::default(),
            )?;
            Ok(s)
        } else {
            Err(MguError::ArgumentError("No terms specified.".to_string()))
        }
    }
}

impl<V, N, T, TF, TyF> Default for PolishNotationEngine<V, N, T, TF, TyF> {
    /// Creates a Polish notation engine with standard Łukasiewicz notation mappings as well as a few additional ones.
    ///
    /// This includes all operators documented in Prior's table (1955) plus
    /// additional operators for arity 0 and 3.
    ///
    #[cfg_attr(doc, doc = include_str!("LUKASIEWICZ_NOTATION.md"))]
    fn default() -> Self {
        use BooleanSimpleOp::*;

        let mut map = HashMap::with_capacity(24);

        // Arity 3 operators
        map.insert('&', And3ABC3);
        map.insert('+', Xor3ABC3);
        map.insert('?', IfABC3);
        map.insert('^', Majority3ABC3);
        map.insert('|', Or3ABC3);

        // Arity 2 operators - Prior's table
        map.insert('A', OrAB2);
        map.insert('B', ImpliesBA2);
        map.insert('C', ImpliesAB2);
        map.insert('D', NotAndAB2);
        map.insert('E', BiimpAB2);
        map.insert('F', NotA2);
        map.insert('G', NotB2);
        map.insert('H', IdB2);
        map.insert('I', IdA2);
        map.insert('J', XorAB2);
        map.insert('K', AndAB2);
        map.insert('L', NotImpliesAB2);
        map.insert('M', NotImpliesBA2);
        map.insert('O', False2);
        map.insert('V', True2);
        map.insert('X', NotOrAB2);

        // Arity 1 operators
        map.insert('N', NotA1);

        // Arity 0 operators
        map.insert('0', False0);
        map.insert('1', True0);

        Self {
            operator_map: map,
            node_map: HashMap::new(),
            var_map: HashMap::new(),
            stack: Vec::new(),
            unused: PhantomData,
            unused2: PhantomData,
        }
    }
}

/// Match invisible characters and semicolon.
///
/// Used to segment hypotheses and assertion from a single string.
fn is_separator(ch: char) -> bool {
    ch.is_whitespace() || ch.is_control() || ch == ';'
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestEngine = PolishNotationEngine<(), (), (), (), ()>;

    #[test]
    fn new_creates_empty_mapping() {
        let engine = TestEngine::new();
        assert_eq!(engine.get_operator('C'), None);
        assert_eq!(engine.get_operator('N'), None);
    }

    #[test]
    fn default_has_standard_mappings() {
        let engine = TestEngine::default();

        // Test a few key operators
        assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));
        assert_eq!(engine.get_operator('N'), Some(&BooleanSimpleOp::NotA1));
        assert_eq!(engine.get_operator('K'), Some(&BooleanSimpleOp::AndAB2));
        assert_eq!(engine.get_operator('A'), Some(&BooleanSimpleOp::OrAB2));
        assert_eq!(engine.get_operator('&'), Some(&BooleanSimpleOp::And3ABC3));
        assert_eq!(engine.get_operator('1'), Some(&BooleanSimpleOp::True0));
    }

    #[test]
    fn insert_valid_character_succeeds() {
        let mut engine = TestEngine::new();
        assert!(engine
            .insert_operator('>', BooleanSimpleOp::ImpliesAB2)
            .is_ok());
        assert_eq!(engine.get_operator('>'), Some(&BooleanSimpleOp::ImpliesAB2));
    }

    #[test]
    fn insert_lowercase_fails() {
        let mut engine = TestEngine::new();
        let result = engine.insert_operator('c', BooleanSimpleOp::ImpliesAB2);
        assert!(result.is_err());
        assert_eq!(engine.get_operator('c'), None);
    }

    #[test]
    fn insert_whitespace_fails() {
        let mut engine = TestEngine::new();
        assert!(engine
            .insert_operator(' ', BooleanSimpleOp::ImpliesAB2)
            .is_err());
        assert!(engine
            .insert_operator('\t', BooleanSimpleOp::ImpliesAB2)
            .is_err());
        assert!(engine
            .insert_operator('\n', BooleanSimpleOp::ImpliesAB2)
            .is_err());
    }

    #[test]
    fn insert_semicolon_fails() {
        let mut engine = TestEngine::new();
        let result = engine.insert_operator(';', BooleanSimpleOp::ImpliesAB2);
        assert!(result.is_err());
    }

    #[test]
    fn insert_control_character_fails() {
        let mut engine = TestEngine::new();
        let result = engine.insert_operator('\u{0003}', BooleanSimpleOp::ImpliesAB2);
        assert!(result.is_err());
    }

    #[test]
    fn clear_state_preserves_operator_map() {
        let mut engine = TestEngine::default();
        assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));

        engine.clear_state();

        // Operator map should still be there
        assert_eq!(engine.get_operator('C'), Some(&BooleanSimpleOp::ImpliesAB2));

        // But internal state should be cleared
        assert!(engine.node_map().is_empty());
        assert!(engine.var_map().is_empty());
        assert!(engine.stack().is_empty());
    }

    #[test]
    fn default_has_all_24_operators() {
        let engine = TestEngine::default();
        // Count should be 24 based on the capacity hint
        assert_eq!(engine.operator_map.len(), 24);
    }
}
