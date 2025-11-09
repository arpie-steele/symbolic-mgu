//! Substitution and normalization for unification.
//!
//! This module provides types for managing term substitutions during unification:
//! - [`Substitution`]: A mapping from metavariables to terms
//! - [`NormalizingSubstitution`]: Maintains substitutions in normal form
//! - [`apply_substitution`]: Applies a substitution to a term

use crate::{Metavariable, MguError, Node, Term, TermFactory, Type};
use std::collections::HashMap;

/// A substitution mapping metavariables to terms.
///
/// This represents a partial function σ: Metavariable → Term.
/// When applied, it recursively replaces metavariables with their mapped terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substitution<V, T>
where
    V: std::hash::Hash + Eq,
    T: PartialEq,
{
    /// The mapping from metavariables to terms.
    map: HashMap<V, T>,
}

impl<V, T> From<HashMap<V, T>> for Substitution<V, T>
where
    V: std::hash::Hash + Eq,
    T: PartialEq,
{
    fn from(value: HashMap<V, T>) -> Self {
        Self { map: value }
    }
}

impl<V, T> Substitution<V, T>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    T: Clone + PartialEq,
{
    /// Create a new empty substitution (identity mapping).
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Get the term mapped to a metavariable, if any.
    pub fn get(&self, var: &V) -> Option<&T> {
        self.map.get(var)
    }

    /// Add a mapping from a metavariable to a term.
    ///
    /// # Errors
    ///
    /// Returns an error if the metavariable is already mapped to a different term.
    pub fn extend(&mut self, var: V, term: T) -> Result<(), MguError> {
        // Rewritten from let-chain for edition 2018 compatibility
        if let Some(existing) = self.map.get(&var) {
            if existing != &term {
                return Err(MguError::UnificationFailure(format!(
                    "Variable {} already mapped to different term",
                    var
                )));
            }
        }
        self.map.insert(var, term);
        Ok(())
    }

    /// Check if this substitution contains a mapping for the given variable.
    pub fn contains(&self, var: &V) -> bool {
        self.map.contains_key(var)
    }

    /// Get the number of mappings in this substitution.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if this substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Get an iterator over the mappings.
    pub fn iter(&self) -> impl Iterator<Item = (&V, &T)> {
        self.map.iter()
    }

    /// Get a mutable iterator over the mappings.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&V, &mut T)> {
        self.map.iter_mut()
    }
}

impl<V, T> Substitution<V, T>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    T: Clone + PartialEq,
{
    /// Ensure this substitution contains no cycles.
    ///
    /// A cycle exists if a variable in the domain maps to a term that (transitively)
    /// contains that same variable. For example:
    /// - `{x ↦ f(x)}` - direct cycle
    /// - `{x ↦ f(y), y ↦ g(x)}` - indirect cycle through y
    ///
    /// Returns `Ok(())` if no cycles detected, or `Err` with the first cycle found.
    ///
    /// # Errors
    ///
    /// It is an error for the substitution of variables to form a loop.
    pub fn ensure_acyclic<Ty, N>(&self) -> Result<(), MguError>
    where
        V: Metavariable<Type = Ty>,
        Ty: Type,
        N: Node<Type = Ty>,
        T: Term<Ty, V, N>,
    {
        // For each variable in the domain, check if it appears in its own transitive closure
        for (var, _term) in self.iter() {
            // Track visited variables to detect cycles
            let mut visited = std::collections::HashSet::new();
            visited.insert(var.clone());

            // Follow the chain starting from this variable's term
            self.check_cycle_from(var, &mut visited)?
        }
        Ok(())
    }

    /// Helper function to check for cycles starting from a variable's mapping.
    ///
    /// Uses depth-first search with a visited set to detect cycles.
    fn check_cycle_from<Ty, N>(
        &self,
        start_var: &V,
        visited: &mut std::collections::HashSet<V>,
    ) -> Result<(), MguError>
    where
        V: Metavariable<Type = Ty>,
        Ty: Type,
        N: Node<Type = Ty>,
        T: Term<Ty, V, N>,
    {
        // Get the term this variable maps to
        if let Some(term) = self.map.get(start_var) {
            // Collect all variables in this term
            let mut vars_in_term = std::collections::HashSet::new();
            term.collect_metavariables(&mut vars_in_term)?;

            // Check each variable in the term
            for var in vars_in_term {
                // If we've already visited this variable, we have a cycle
                if visited.contains(&var) {
                    return Err(MguError::SubstitutionCycle(format!(
                        "Variable {} appears in its own definition chain",
                        var
                    )));
                }

                // If this variable has a mapping, follow it
                if self.map.contains_key(&var) {
                    visited.insert(var.clone());
                    self.check_cycle_from::<Ty, N>(&var, visited)?;
                    visited.remove(&var);
                }
            }
        }
        Ok(())
    }
}

impl<V, T> Default for Substitution<V, T>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    T: Clone + PartialEq,
{
    fn default() -> Self {
        Self::new()
    }
}

/// A wrapper around Substitution that maintains the normal form invariant.
///
/// This wrapper has access to the N: Node type parameter, allowing it to
/// normalize the substitution after each extension. A substitution is in
/// normal form when no variable in the domain appears in any term in the range.
///
/// When adding a binding `v ↦ t`, we apply this new binding to all existing
/// values in the substitution, eliminating chains like:
/// ```text
/// {P ↦ (T → S), T ↦ (Q → R), Q ↦ U}
/// ```
/// which should be normalized to:
/// ```text
/// {P ↦ (((U → R) → S)), T ↦ (U → R), Q ↦ U}
/// ```
pub struct NormalizingSubstitution<V, N, T, TF>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    N: Node<Type = V::Type>,
    T: Term<V::Type, V, N> + Clone + PartialEq,
    TF: TermFactory<T, V::Type, V, N, Term = T, TermNode = N>,
{
    /// The underlying substitution being maintained in normal form
    inner: Substitution<V, T>,
    /// `PhantomData` to hold the Node type parameter
    _phantom_node: std::marker::PhantomData<N>,
    /// `PhantomData` to hold the `TermFactory` type parameter
    _phantom_factory: std::marker::PhantomData<TF>,
}

impl<V, N, T, TF> NormalizingSubstitution<V, N, T, TF>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    N: Node<Type = V::Type>,
    T: Term<V::Type, V, N> + Clone + PartialEq,
    TF: TermFactory<T, V::Type, V, N, Term = T, TermNode = N>,
{
    /// Create a new empty normalizing substitution.
    pub fn new() -> Self {
        Self {
            inner: Substitution::new(),
            _phantom_node: std::marker::PhantomData,
            _phantom_factory: std::marker::PhantomData,
        }
    }

    /// Create from an existing substitution (assumes it's already in normal form).
    pub fn from_substitution(subst: Substitution<V, T>) -> Self {
        Self {
            inner: subst,
            _phantom_node: std::marker::PhantomData,
            _phantom_factory: std::marker::PhantomData,
        }
    }

    /// Safely promote a Substitution to a `NormalizingSubstitution`.
    ///
    /// This method:
    /// 1. Checks for cycles in the input substitution
    /// 2. Normalizes by replaying all bindings through `extend()`, which normalizes incrementally
    /// 3. Returns Ok(`NormalizingSubstitution`) if successful
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The substitution contains cycles (would never terminate)
    /// - Normalization fails during term reconstruction
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // Create a substitution with chains (but no cycles)
    /// let mut subst = Substitution::new();
    /// // {P ↦ (T → S), T ↦ (Q → R), Q ↦ U}
    ///
    /// // Normalize it
    /// let normalized = NormalizingSubstitution::try_normalize(factory, subst)?;
    /// // Result: {P ↦ (((U → R) → S)), T ↦ (U → R), Q ↦ U}
    /// ```
    pub fn try_normalize(factory: &TF, subst: Substitution<V, T>) -> Result<Self, MguError> {
        // First ensure no cycles
        subst.ensure_acyclic()?;

        // Create a new normalizing substitution and replay all bindings
        // Each extend() will normalize as it goes
        let mut normalized = Self::new();

        for (var, term) in subst.iter() {
            normalized.extend(factory, var.clone(), term.clone())?;
        }

        Ok(normalized)
    }

    /// Convert back to a plain Substitution.
    pub fn into_inner(self) -> Substitution<V, T> {
        self.inner
    }

    /// Add a mapping from a metavariable to a term, maintaining normal form.
    ///
    /// After adding `v ↦ t`, we apply this binding to all existing values
    /// in the substitution to ensure no variable in the domain appears in the range.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The metavariable is already mapped to a different term
    /// - Normalization fails during substitution application
    pub fn extend(&mut self, factory: &TF, var: V, term: T) -> Result<(), MguError> {
        // Check for conflicts - rewritten from let-chain for edition 2018 compatibility
        if let Some(existing) = self.inner.map.get(&var) {
            if existing != &term {
                return Err(MguError::UnificationFailure(format!(
                    "Variable {} already mapped to different term",
                    var
                )));
            }
        }

        // Add the new binding
        self.inner.map.insert(var.clone(), term.clone());

        // Normalize: apply the new binding to all OTHER existing values
        // Collect keys first to avoid borrowing issues
        let vars_to_normalize: Vec<V> = self
            .inner
            .map
            .keys()
            .filter(|k| {
                // Only normalize other variables, not the one we just added
                if let Ok((k_type, k_index)) = k.get_type_and_index() {
                    if let Ok((var_type, var_index)) = var.get_type_and_index() {
                        k_type != var_type || k_index != var_index
                    } else {
                        false
                    }
                } else {
                    false
                }
            })
            .cloned()
            .collect();

        // Apply the new binding to each existing value
        for key in vars_to_normalize {
            if let Some(existing_term) = self.inner.map.get(&key).cloned() {
                // Create a temporary substitution with just the new binding
                let mut temp_subst = Substitution::new();
                temp_subst.map.insert(var.clone(), term.clone());

                // Apply it to normalize this existing term
                let normalized = apply_substitution(factory, &temp_subst, &existing_term)?;

                // Update the mapping with the normalized term
                self.inner.map.insert(key, normalized);
            }
        }

        Ok(())
    }

    /// Clone the underlying substitution.
    pub fn clone_inner(&self) -> Substitution<V, T> {
        self.inner.clone()
    }
}

impl<V, N, T, TF> Default for NormalizingSubstitution<V, N, T, TF>
where
    V: Metavariable + std::hash::Hash + Eq + Clone,
    N: Node<Type = V::Type>,
    T: Term<V::Type, V, N> + Clone + PartialEq,
    TF: TermFactory<T, V::Type, V, N, Term = T, TermNode = N>,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Check if a metavariable occurs anywhere in a term (occurs check).
///
/// This prevents creating cyclic substitutions like x ↦ f(x).
///
/// # Errors
///
/// Returns an error if metavariable extraction fails.
pub fn occurs_check<V, Ty, N, T>(var: &V, term: &T) -> Result<bool, MguError>
where
    V: Metavariable<Type = Ty> + Clone,
    Ty: Type,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    // If the term is a metavariable, check if it's the same variable
    // Rewritten from let-chain for edition 2018 compatibility
    if term.is_metavariable() {
        if let Some(term_var) = term.get_metavariable() {
            // Need to compare the metavariables
            let (var_type, var_index) = var.get_type_and_index()?;
            let (term_type, term_index) = term_var.get_type_and_index()?;
            return Ok(var_type == term_type && var_index == term_index);
        }
    }

    // Recursively check all children
    for child in term.get_children() {
        if occurs_check(var, child)? {
            return Ok(true);
        }
    }

    Ok(false)
}

/// Apply a substitution to a term, replacing metavariables with their mapped terms.
///
/// Uses the factory pattern to construct new terms with substituted children.
///
/// # Errors
///
/// Returns an error if term construction or type checking fails.
pub fn apply_substitution<V, Ty, N, T, TF>(
    factory: &TF,
    subst: &Substitution<V, T>,
    term: &T,
) -> Result<T, MguError>
where
    V: Metavariable<Type = Ty> + std::hash::Hash + Eq + Clone,
    Ty: Type,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N> + Clone + PartialEq,
    TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N>,
{
    // If this is a metavariable, check if it's in the substitution
    if term.is_metavariable() {
        if let Some(var) = term.get_metavariable() {
            let (var_type, var_index) = var.get_type_and_index()?;

            // Look for this variable in the substitution map
            for (subst_var, subst_term) in subst.iter() {
                let (subst_type, subst_index) = subst_var.get_type_and_index()?;
                if var_type == subst_type && var_index == subst_index {
                    // Found it - return the substituted term
                    // We don't recursively apply because we assume the substitution
                    // is already in normal form (no chains)
                    return Ok(subst_term.clone());
                }
            }
        }
        // Variable not in substitution, return as-is
        return Ok(term.clone());
    }

    // This is a node with children - recursively apply to children
    if let Some(node) = term.get_node() {
        let mut new_children = Vec::new();
        for child in term.get_children() {
            new_children.push(apply_substitution(factory, subst, child)?);
        }

        factory.create_node(node, new_children)
    } else {
        Err(MguError::UnificationFailure(
            "Non-metavariable term has no node".to_string(),
        ))
    }
}

/// Compute the most general unifier of two terms.
///
/// This implements Robinson's unification algorithm:
/// 1. If both are identical, return empty substitution
/// 2. If one is a variable, bind it to the other (with occurs check)
/// 3. If both are nodes with the same root, recursively unify children
/// 4. Otherwise, unification fails
///
/// # Errors
///
/// Returns an error if:
/// - Terms have incompatible types
/// - Nodes don't match
/// - Occurs check fails (would create cyclic substitution)
/// - Type constraints are violated
pub fn unify<V, Ty, N, T, TF>(
    factory: &TF,
    term1: &T,
    term2: &T,
) -> Result<Substitution<V, T>, MguError>
where
    V: Metavariable<Type = Ty> + std::hash::Hash + Eq + Clone,
    Ty: Type,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N> + Clone + PartialEq,
    TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N>,
{
    unify_with_subst(factory, &Substitution::new(), term1, term2)
}

/// Compute the MGU given an existing substitution.
///
/// This is the workhorse function that accumulates substitutions as it recurses.
/// Uses `NormalizingSubstitution` internally to maintain the invariant that
/// substitutions are always in normal form (no variable in domain appears in range).
///
/// # Errors
///
/// Returns an error if unification fails.
fn unify_with_subst<V, Ty, N, T, TF>(
    factory: &TF,
    subst: &Substitution<V, T>,
    term1: &T,
    term2: &T,
) -> Result<Substitution<V, T>, MguError>
where
    V: Metavariable<Type = Ty> + std::hash::Hash + Eq + Clone,
    Ty: Type,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N> + Clone + PartialEq,
    TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N>,
{
    // Convert to normalizing substitution for internal use
    let mut norm_subst = NormalizingSubstitution::<V, N, T, TF>::from_substitution(subst.clone());

    // First, apply current substitution to both terms
    let t1 = apply_substitution(factory, subst, term1)?;
    let t2 = apply_substitution(factory, subst, term2)?;

    // If terms are identical, we're done
    if t1 == t2 {
        return Ok(subst.clone());
    }

    // Case 1: `t1` is a metavariable
    // Rewritten from let-chain for edition 2018 compatibility
    if t1.is_metavariable() {
        if let Some(var1) = t1.get_metavariable() {
            // Type check: can `var1`'s type accept `t2`'s type?
            // This enforces: Setvar ↦ Class is OK, but Class ↦ Setvar is forbidden
            let var1_type = var1.get_type()?;
            let t2_type = t2.get_type()?;
            if !t2_type.is_subtype_of(&var1_type) {
                return Err(MguError::from_found_and_expected_types(
                    true, &t2_type, &var1_type,
                ));
            }

            // Occurs check: make sure var1 doesn't appear in `t2`
            if occurs_check(&var1, &t2)? {
                return Err(MguError::UnificationFailure(
                    "Occurs check failed: variable appears in term it would be bound to"
                        .to_string(),
                ));
            }

            // Add the binding using normalizing wrapper
            norm_subst.extend(factory, var1, t2)?;
            return Ok(norm_subst.into_inner());
        }
    }

    // Case 2: `t2` is a metavariable
    // Rewritten from let-chain for edition 2018 compatibility
    if t2.is_metavariable() {
        if let Some(var2) = t2.get_metavariable() {
            // Type check: can `var2`'s type accept `t1`'s type?
            let var2_type = var2.get_type()?;
            let t1_type = t1.get_type()?;
            if !t1_type.is_subtype_of(&var2_type) {
                return Err(MguError::from_found_and_expected_types(
                    true, &t1_type, &var2_type,
                ));
            }

            // Occurs check
            if occurs_check(&var2, &t1)? {
                return Err(MguError::UnificationFailure(
                    "Occurs check failed: variable appears in term it would be bound to"
                        .to_string(),
                ));
            }

            // Add the binding using normalizing wrapper
            norm_subst.extend(factory, var2, t1)?;
            return Ok(norm_subst.into_inner());
        }
    }

    // Case 3: Both are nodes - they must have the same root
    let node1 = t1
        .get_node()
        .ok_or_else(|| MguError::UnificationFailure("Expected node in term1".to_string()))?;
    let node2 = t2
        .get_node()
        .ok_or_else(|| MguError::UnificationFailure("Expected node in term2".to_string()))?;

    let node1_index = node1.get_index()?;
    let node1_type = node1.get_type()?;
    let node2_index = node2.get_index()?;
    let node2_type = node2.get_type()?;

    // Nodes must match
    if node1_type != node2_type || node1_index != node2_index {
        return Err(MguError::UnificationFailure(format!(
            "Node mismatch: ({:?}, {}) vs ({:?}, {})",
            node1_type, node1_index, node2_type, node2_index
        )));
    }

    // Arity must match
    let n_children = t1.get_n_children();
    if n_children != t2.get_n_children() {
        return Err(MguError::SlotsMismatch(
            t1.get_n_children(),
            t2.get_n_children(),
        ));
    }

    // Recursively unify all children
    let mut current_subst = subst.clone();
    for i in 0..n_children {
        let child1 = t1
            .get_child(i)
            .ok_or(MguError::ChildIndexOutOfRange(i, n_children))?;
        let child2 = t2
            .get_child(i)
            .ok_or(MguError::ChildIndexOutOfRange(i, n_children))?;

        current_subst = unify_with_subst(factory, &current_subst, child1, child2)?;
    }

    Ok(current_subst)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EnumTerm, MetaByte, MetavariableFactory, NodeByte, NodeFactory, SimpleType};

    type TestTerm = EnumTerm<SimpleType, MetaByte, NodeByte>;

    /// Minimal `TermFactory` implementation for testing
    #[derive(Debug)]
    struct TestTermFactory;

    impl TermFactory<TestTerm, SimpleType, MetaByte, NodeByte> for TestTermFactory {
        type TermType = SimpleType;
        type Term = TestTerm;
        type TermNode = NodeByte;
        type TermMetavariable = MetaByte;

        fn from_factories<VF, NF>(_vars: VF, _nodes: NF) -> Self
        where
            VF: MetavariableFactory<Metavariable = MetaByte>,
            NF: NodeFactory<Node = NodeByte>,
        {
            TestTermFactory
        }

        fn create_leaf(&self, var: Self::TermMetavariable) -> Result<Self::Term, MguError> {
            Ok(TestTerm::Leaf(var))
        }

        fn create_node(
            &self,
            node: Self::TermNode,
            children: Vec<Self::Term>,
        ) -> Result<Self::Term, MguError> {
            // Validate arity
            let expected_arity = node.get_arity()?;
            if children.len() != expected_arity {
                return Err(MguError::SlotsMismatch(expected_arity, children.len()));
            }
            Ok(TestTerm::NodeOrLeaf(node, children))
        }
    }

    #[test]
    fn empty_substitution() {
        let subst: Substitution<MetaByte, TestTerm> = Substitution::new();
        assert!(subst.is_empty());
        assert_eq!(subst.len(), 0);
    }

    #[test]
    fn single_binding() {
        let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let term = TestTerm::Leaf(var);

        let mut subst = Substitution::new();
        assert!(subst.extend(var, term.clone()).is_ok());
        assert_eq!(subst.len(), 1);
        assert!(subst.contains(&var));
        assert_eq!(subst.get(&var), Some(&term));
    }

    #[test]
    fn identical_terms_unify() {
        let factory = TestTermFactory;
        let var1 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var1);

        let result = unify(&factory, &term1, &term2);
        assert!(result.is_ok());
        let subst = result.unwrap();
        assert!(subst.is_empty());
    }

    #[test]
    fn different_variables_unify() {
        let factory = TestTermFactory;
        let var1 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let var2 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 1).unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var2);

        let result = unify(&factory, &term1, &term2);
        assert!(result.is_ok());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn type_mismatch_fails() {
        let factory = TestTermFactory;
        let var_bool = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let var_class = MetaByte::try_from_type_and_index(SimpleType::Class, 0).unwrap();
        let term_bool = TestTerm::Leaf(var_bool);
        let term_class = TestTerm::Leaf(var_class);

        let result = unify(&factory, &term_bool, &term_class);
        assert!(result.is_err());
    }

    #[test]
    fn occurs_check_detects_cycle() {
        let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let term_var = TestTerm::Leaf(var);

        // Create term: Not(var)
        let not_node = NodeByte::Not;
        let term_not = TestTerm::NodeOrLeaf(not_node, vec![term_var.clone()]);

        // Occurs check should detect that var appears in Not(var)
        let result = occurs_check(&var, &term_not);
        assert!(result.is_ok());
        assert!(result.unwrap());
    }

    #[test]
    fn occurs_check_prevents_unification() {
        let factory = TestTermFactory;
        let var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let term_var = TestTerm::Leaf(var);

        // Create term: Not(var)
        let not_node = NodeByte::Not;
        let term_not = TestTerm::NodeOrLeaf(not_node, vec![term_var.clone()]);

        // Trying to unify var with Not(var) should fail
        let result = unify(&factory, &term_var, &term_not);
        assert!(result.is_err());
    }

    #[test]
    fn apply_substitution_to_var() {
        let factory = TestTermFactory;
        let var1 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let var2 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 1).unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var2);

        let mut subst = Substitution::new();
        subst.extend(var1, term2.clone()).unwrap();

        let result = apply_substitution(&factory, &subst, &term1);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), term2);
    }

    #[test]
    fn apply_substitution_to_node() {
        let factory = TestTermFactory;
        let var1 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let var2 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 1).unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var2);

        // Create And(var1, var1)
        let and_node = NodeByte::And;
        let and_term = TestTerm::NodeOrLeaf(and_node, vec![term1.clone(), term1.clone()]);

        // Substitution: map var1 to var2
        let mut subst = Substitution::new();
        subst.extend(var1, term2.clone()).unwrap();

        // Apply should give And(var2, var2)
        let result = apply_substitution(&factory, &subst, &and_term);
        assert!(result.is_ok());
        let result_term = result.unwrap();

        let expected = TestTerm::NodeOrLeaf(and_node, vec![term2.clone(), term2.clone()]);
        assert_eq!(result_term, expected);
    }
}
