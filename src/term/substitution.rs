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
    #[must_use]
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Get the term mapped to a metavariable, if any.
    #[must_use]
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
    #[must_use]
    pub fn contains(&self, var: &V) -> bool {
        self.map.contains_key(var)
    }

    /// Get the number of mappings in this substitution.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if this substitution is empty.
    #[must_use]
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
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Substitution::new(),
            _phantom_node: std::marker::PhantomData,
            _phantom_factory: std::marker::PhantomData,
        }
    }

    /// Create from an existing substitution (assumes it's already in normal form).
    #[must_use]
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
    /// ```rust,compile_fail
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
    #[must_use]
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
        let term = apply_substitution(factory, &self.clone_inner(), &term)?;
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
    #[must_use]
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
    if let Some(term_var) = term.get_metavariable() {
        // Need to compare the metavariables
        let (var_type, var_index) = var.get_type_and_index()?;
        let (term_type, term_index) = term_var.get_type_and_index()?;
        return Ok(var_type == term_type && var_index == term_index);
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
    if let Some(var1) = t1.get_metavariable() {
        let t1_type = t1.get_type()?;
        let t2_type = t2.get_type()?;
        if let Some(var2) = t2.get_metavariable() {
            // Case `1a`: `t1` and `t2` are metavariables

            // Type check: can `var1`'s type accept `t2`'s type?
            // This enforces: Setvar ↦ Class is OK, but Class ↦ Setvar is forbidden
            if t2_type.is_subtype_of(&t1_type) {
                // Occurs check: make sure `var1` doesn't appear in `t2`
                if occurs_check(&var1, &t2)? {
                    return Err(MguError::UnificationFailure(
                        "Occurs check failed: variable appears in term it would be bound to"
                            .to_string(),
                    ));
                }
                // Add the binding using normalizing wrapper
                norm_subst.extend(factory, var1, t2)?;
                return Ok(norm_subst.into_inner());
            } else if t1_type.is_subtype_of(&t2_type) {
                // Occurs check: make sure `var2` doesn't appear in `t1`
                if occurs_check(&var2, &t1)? {
                    return Err(MguError::UnificationFailure(
                        "Occurs check failed: variable appears in term it would be bound to"
                            .to_string(),
                    ));
                }

                // Add the binding using normalizing wrapper
                norm_subst.extend(factory, var2, t1)?;
                return Ok(norm_subst.into_inner());
            } else {
                return Err(MguError::UnificationFailure(format!(
                    "Metavariables {} and {} have incompatible types and cannot be unified.",
                    var1, var2
                )));
            }
        }

        // Case `1b`: `t1` is a metavariable and `t2` is a node
        if !t2_type.is_subtype_of(&t1_type) {
            return Err(MguError::from_found_and_expected_types(
                true, &t2_type, &t1_type,
            ));
        }

        // Occurs check: make sure `var1` doesn't appear in `t2`
        if occurs_check(&var1, &t2)? {
            return Err(MguError::UnificationFailure(
                "Occurs check failed: variable appears in term it would be bound to".to_string(),
            ));
        }

        // Add the binding using normalizing wrapper
        norm_subst.extend(factory, var1, t2)?;
        return Ok(norm_subst.into_inner());
    }

    // Case 2: `t2` is a metavariable
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
                "Occurs check failed: variable appears in term it would be bound to".to_string(),
            ));
        }

        // Add the binding using normalizing wrapper
        norm_subst.extend(factory, var2, t1)?;
        return Ok(norm_subst.into_inner());
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
        return Err(MguError::from_found_and_expected_unsigned(
            t1.get_n_children(),
            t2.get_n_children(),
        ));
    }

    // Recursively unify all children
    let mut current_subst = subst.clone();
    for i in 0..n_children {
        let child1 = t1
            .get_child(i)
            .ok_or_else(|| MguError::from_index_and_len(i, n_children))?;
        let child2 = t2
            .get_child(i)
            .ok_or_else(|| MguError::from_index_and_len(i, n_children))?;

        current_subst = unify_with_subst(factory, &current_subst, child1, child2)?;
    }

    Ok(current_subst)
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;
    use crate::{
        EnumTerm, MetaByte, MetaByteFactory, MetavariableFactory, NodeByte, NodeFactory, SimpleType,
    };

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
                return Err(MguError::from_found_and_expected_unsigned(
                    expected_arity,
                    children.len(),
                ));
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
        let vars = MetaByteFactory();
        let (var, other_var) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let term = TestTerm::Leaf(var);
        let other_term = TestTerm::Leaf(other_var);

        let mut subst = Substitution::new();
        assert!(subst.extend(var, term.clone()).is_ok());
        assert_eq!(subst.len(), 1);
        assert!(subst.contains(&var));
        assert_eq!(subst.get(&var), Some(&term));

        assert!(subst.extend(var, term.clone()).is_ok());
        assert_eq!(subst.len(), 1);
        assert!(subst.contains(&var));
        assert_eq!(subst.get(&var), Some(&term));

        assert!(subst.extend(var, other_term.clone()).is_err());
        assert_eq!(subst.len(), 1);
        assert!(subst.contains(&var));
        assert_eq!(subst.get(&var), Some(&term));
    }

    #[test]
    fn identical_terms_unify() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let var1 = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();
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
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
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
        let vars = MetaByteFactory();
        let var_bool = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();
        let var_class = vars
            .list_metavariables_by_type(&SimpleType::Class)
            .next()
            .unwrap();
        let term_bool = TestTerm::Leaf(var_bool);
        let term_class = TestTerm::Leaf(var_class);

        let result = unify(&factory, &term_bool, &term_class);
        assert!(result.is_err());
    }

    #[test]
    fn occurs_check_detects_cycle() {
        let var = MetaByteFactory()
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();
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
        let vars = MetaByteFactory();
        let var = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();
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
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
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
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var2);

        // Create And(`var1`, `var1`)
        let and_node = NodeByte::And;
        let and_term = TestTerm::NodeOrLeaf(and_node, vec![term1.clone(), term1.clone()]);

        // Substitution: map `var1` to `var2`
        let mut subst = Substitution::new();
        subst.extend(var1, term2.clone()).unwrap();

        // Apply should give And(`var2`, `var2`)
        let result = apply_substitution(&factory, &subst, &and_term);
        assert!(result.is_ok());
        let result_term = result.unwrap();

        let expected = TestTerm::NodeOrLeaf(and_node, vec![term2.clone(), term2.clone()]);
        assert_eq!(result_term, expected);
    }

    #[test]
    fn substitution_iter() {
        let vars = MetaByteFactory();
        let mut var_iter = vars.list_metavariables_by_type(&SimpleType::Boolean);
        let var1 = var_iter.next().unwrap();
        let var2 = var_iter.next().unwrap();
        let var3 = var_iter.next().unwrap();
        let var4 = var_iter.next().unwrap();

        let term1 = TestTerm::Leaf(var2);
        let term2 = TestTerm::Leaf(var3);
        let term3 = TestTerm::Leaf(var4);

        let mut subst = Substitution::new();
        subst.extend(var1, term1.clone()).unwrap();
        subst.extend(var2, term2.clone()).unwrap();
        subst.extend(var3, term3.clone()).unwrap();

        // Test iter()
        let collected: Vec<_> = subst.iter().collect();
        assert_eq!(collected.len(), 3);

        // Verify all mappings are present
        assert!(collected.iter().any(|(v, _)| **v == var1));
        assert!(collected.iter().any(|(v, _)| **v == var2));
        assert!(collected.iter().any(|(v, _)| **v == var3));
    }

    #[test]
    fn substitution_iter_mut() {
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let term1 = TestTerm::Leaf(var1);
        let term2 = TestTerm::Leaf(var2);

        let mut subst = Substitution::new();
        subst.extend(var1, term1.clone()).unwrap();

        // Mutate through `iter_mut`
        for (_var, term) in subst.iter_mut() {
            *term = term2.clone();
        }

        // Verify mutation
        assert_eq!(subst.get(&var1), Some(&term2));
    }

    #[test]
    fn ensure_acyclic_direct_cycle() {
        let vars = MetaByteFactory();
        let var1 = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();

        // Create term: Not(`var1`), forming cycle `{var1 ↦ Not(var1)}`
        let not_node = NodeByte::Not;
        let term_not = TestTerm::NodeOrLeaf(not_node, vec![TestTerm::Leaf(var1)]);

        let mut subst = Substitution::new();
        subst.extend(var1, term_not).unwrap();

        // `ensure_acyclic` should detect the direct cycle
        let result = subst.ensure_acyclic::<SimpleType, NodeByte>();
        assert!(
            result.is_err(),
            "{}",
            &"ensure_acyclic should detect direct cycle {var1 ↦ Not(var1)}"
        );
    }

    #[test]
    fn ensure_acyclic_two_element_cycle() {
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create cycle: `{var1 ↦ Not(var2), var2 ↦ Not(var1)}`
        let not_node = NodeByte::Not;
        let term1 = TestTerm::NodeOrLeaf(not_node, vec![TestTerm::Leaf(var2)]);
        let term2 = TestTerm::NodeOrLeaf(not_node, vec![TestTerm::Leaf(var1)]);

        let mut subst = Substitution::new();
        subst.extend(var1, term1).unwrap();
        subst.extend(var2, term2).unwrap();

        // `ensure_acyclic` should detect the two-element cycle
        let result = subst.ensure_acyclic::<SimpleType, NodeByte>();
        assert!(
            result.is_err(),
            "ensure_acyclic should detect two-element cycle"
        );
    }

    #[test]
    fn ensure_acyclic_longer_chain_cycle() {
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create cycle: `{var1 ↦ var2, var2 ↦ var3, var3 ↦ var1}`
        let term1 = TestTerm::Leaf(var2);
        let term2 = TestTerm::Leaf(var3);
        let term3 = TestTerm::Leaf(var1);

        let mut subst = Substitution::new();
        subst.extend(var1, term1).unwrap();
        subst.extend(var2, term2).unwrap();
        subst.extend(var3, term3).unwrap();

        // `ensure_acyclic` should detect the three-element cycle
        let result = subst.ensure_acyclic::<SimpleType, NodeByte>();
        assert!(
            result.is_err(),
            "ensure_acyclic should detect three-element cycle"
        );
    }

    #[test]
    fn ensure_acyclic_accepts_acyclic() {
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create acyclic chain: `{var1 ↦ var2, var2 ↦ var3}`
        let term1 = TestTerm::Leaf(var2);
        let term2 = TestTerm::Leaf(var3);

        let mut subst = Substitution::new();
        subst.extend(var1, term1).unwrap();
        subst.extend(var2, term2).unwrap();

        // `ensure_acyclic` should accept this
        let result = subst.ensure_acyclic::<SimpleType, NodeByte>();
        assert!(result.is_ok(), "ensure_acyclic should accept acyclic chain");
    }

    #[test]
    fn normalizing_substitution_simple_chain() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create chain: `{var1 ↦ var2, var2 ↦ var3}`
        let mut norm_subst = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();

        norm_subst
            .extend(&factory, var1, TestTerm::Leaf(var2))
            .unwrap();
        norm_subst
            .extend(&factory, var2, TestTerm::Leaf(var3))
            .unwrap();

        // After normalization: `{var1 ↦ var3, var2 ↦ var3}`
        let inner = norm_subst.clone_inner();
        assert_eq!(inner.get(&var1), Some(&TestTerm::Leaf(var3)));
        assert_eq!(inner.get(&var2), Some(&TestTerm::Leaf(var3)));
    }

    #[test]
    fn normalizing_substitution_complex_chain() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var_p, var_t, var_s, var_q) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create: {P ↦ (T → S), T ↦ Q}
        let implies_node = NodeByte::Implies;
        let term_implies = TestTerm::NodeOrLeaf(
            implies_node,
            vec![TestTerm::Leaf(var_t), TestTerm::Leaf(var_s)],
        );

        let mut norm_subst = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();

        norm_subst.extend(&factory, var_p, term_implies).unwrap();
        norm_subst
            .extend(&factory, var_t, TestTerm::Leaf(var_q))
            .unwrap();

        // After normalization: {P ↦ (Q → S), T ↦ Q}
        let inner = norm_subst.clone_inner();
        let expected_p = TestTerm::NodeOrLeaf(
            implies_node,
            vec![TestTerm::Leaf(var_q), TestTerm::Leaf(var_s)],
        );
        assert_eq!(inner.get(&var_p), Some(&expected_p));
        assert_eq!(inner.get(&var_t), Some(&TestTerm::Leaf(var_q)));
    }

    #[test]
    fn normalizing_substitution_extend() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2, var3, var4) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();
        let term1 = factory.create_leaf(var1);
        assert!(term1.is_ok());
        let term1 = term1.unwrap();
        let term2 = factory.create_leaf(var2);
        assert!(term2.is_ok());
        let term2 = term2.unwrap();
        let term3 = factory.create_leaf(var3);
        assert!(term3.is_ok());
        let term3 = term3.unwrap();
        let term4 = factory.create_leaf(var4);
        assert!(term4.is_ok());
        let term4 = term4.unwrap();

        let mut subst = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();
        assert!(subst.extend(&factory, var1, term2.clone()).is_ok());
        assert_eq!(subst.clone_inner().len(), 1);
        assert!(subst.clone_inner().contains(&var1));
        assert_eq!(subst.clone_inner().get(&var1), Some(&term2));

        assert!(subst.extend(&factory, var1, term2.clone()).is_ok());
        assert_eq!(subst.clone_inner().len(), 1);
        assert!(subst.clone_inner().contains(&var1));
        assert_eq!(subst.clone_inner().get(&var1), Some(&term2));

        assert!(subst.extend(&factory, var1, term3.clone()).is_err());
        assert_eq!(subst.clone_inner().len(), 1);
        assert!(subst.clone_inner().contains(&var1));
        assert_eq!(subst.clone_inner().get(&var1), Some(&term2));

        assert!(subst.extend(&factory, var3, term1.clone()).is_ok());
        assert_eq!(subst.clone_inner().len(), 2);
        assert!(subst.clone_inner().contains(&var1));
        assert!(subst.clone_inner().contains(&var3));
        assert_eq!(subst.clone_inner().get(&var1), Some(&term2));
        assert_eq!(subst.clone_inner().get(&var3), Some(&term2));

        assert!(subst.extend(&factory, var2, term4.clone()).is_ok());
        assert_eq!(subst.clone_inner().len(), 3);
        assert!(subst.clone_inner().contains(&var1));
        assert!(subst.clone_inner().contains(&var2));
        assert!(subst.clone_inner().contains(&var3));
        assert_eq!(subst.clone_inner().get(&var1), Some(&term4));
        assert_eq!(subst.clone_inner().get(&var2), Some(&term4));
        assert_eq!(subst.clone_inner().get(&var3), Some(&term4));
    }

    #[test]
    fn normalizing_substitution_order_independence() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Order 1: `{var1 ↦ var2, var2 ↦ var3}`
        let mut subst1 = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();
        subst1.extend(&factory, var1, TestTerm::Leaf(var2)).unwrap();
        subst1.extend(&factory, var2, TestTerm::Leaf(var3)).unwrap();

        // Order 2: `{var2 ↦ var3, var1 ↦ var2}`
        let mut subst2 = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();
        subst2.extend(&factory, var2, TestTerm::Leaf(var3)).unwrap();
        subst2.extend(&factory, var1, TestTerm::Leaf(var2)).unwrap();

        // Both should normalize to `{var1 ↦ var3, var2 ↦ var3}`
        let inner1 = subst1.clone_inner();
        let inner2 = subst2.clone_inner();

        assert_eq!(inner1.get(&var1), Some(&TestTerm::Leaf(var3)));
        assert_eq!(inner1.get(&var2), Some(&TestTerm::Leaf(var3)));
        assert_eq!(inner2.get(&var1), Some(&TestTerm::Leaf(var3)));
        assert_eq!(inner2.get(&var2), Some(&TestTerm::Leaf(var3)));
    }

    #[test]
    fn normalizing_substitution_try_normalize() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create plain substitution with chain
        let mut plain_subst = Substitution::new();
        plain_subst.extend(var1, TestTerm::Leaf(var2)).unwrap();
        plain_subst.extend(var2, TestTerm::Leaf(var3)).unwrap();

        // Normalize using `try_normalize`
        let norm_result = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::try_normalize(
            &factory,
            plain_subst,
        );
        assert!(norm_result.is_ok());

        let norm_subst = norm_result.unwrap();
        let inner = norm_subst.into_inner();

        // Should be normalized
        assert_eq!(inner.get(&var1), Some(&TestTerm::Leaf(var3)));
        assert_eq!(inner.get(&var2), Some(&TestTerm::Leaf(var3)));
    }

    #[test]
    fn normalizing_substitution_try_normalize_rejects_cycle() {
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create cyclic substitution
        let mut plain_subst = Substitution::new();
        plain_subst.extend(var1, TestTerm::Leaf(var2)).unwrap();
        plain_subst.extend(var2, TestTerm::Leaf(var1)).unwrap();

        // `try_normalize` should reject cycles
        let norm_result = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::try_normalize(
            &factory,
            plain_subst,
        );
        assert!(
            norm_result.is_err(),
            "try_normalize should reject cyclic substitution"
        );
    }

    // =========================================================================
    // Error Path Tests
    // =========================================================================

    #[test]
    fn normalizing_substitution_extend_conflict() {
        // Test that NormalizingSubstitution::extend() properly detects
        // conflicting bindings (lines 298-303)
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let (var1, var2, var3) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        let mut norm_subst = NormalizingSubstitution::<_, NodeByte, _, TestTermFactory>::new();

        // First binding: `var1` ↦ `var2`
        norm_subst
            .extend(&factory, var1, TestTerm::Leaf(var2))
            .unwrap();

        // Try to add conflicting binding: `var1` ↦ `var3` (should fail)
        let result = norm_subst.extend(&factory, var1, TestTerm::Leaf(var3));

        assert!(
            result.is_err(),
            "Should reject conflicting binding for same variable"
        );

        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("already mapped to different term"),
            "Error should mention conflicting mapping, got: {}",
            err_msg
        );
    }

    #[test]
    fn occurs_check_reverse_case() {
        // Test occurs check when the second term is the variable
        // (unifying f(x) with x, not just x with f(x))
        let factory = TestTermFactory;
        let vars = MetaByteFactory();
        let var = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();

        let var_term = TestTerm::Leaf(var);
        let not_node = NodeByte::Not;
        let not_var = TestTerm::NodeOrLeaf(not_node, vec![var_term.clone()]);

        // Unify Not(var) with var (reverse of usual occurs check test)
        let result = unify(&factory, &not_var, &var_term);

        assert!(
            result.is_err(),
            "Should fail occurs check when second term is variable"
        );

        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("Occurs check failed"),
            "Error should mention occurs check, got: {}",
            err_msg
        );
    }

    #[test]
    fn type_error_both_directions() {
        // Test type mismatch errors in both directions of unification
        let factory = TestTermFactory;
        let vars = MetaByteFactory();

        let var_bool = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();
        let var_class = vars
            .list_metavariables_by_type(&SimpleType::Class)
            .next()
            .unwrap();

        let term_bool = TestTerm::Leaf(var_bool);
        let term_class = TestTerm::Leaf(var_class);

        // Test both directions
        let result1 = unify(&factory, &term_bool, &term_class);
        let result2 = unify(&factory, &term_class, &term_bool);

        assert!(
            result1.is_err(),
            "Boolean ↔ Class should fail (direction 1)"
        );
        assert!(
            result2.is_err(),
            "Boolean ↔ Class should fail (direction 2)"
        );
    }

    #[test]
    fn unify_setvar_with_class_variable() {
        // Test that Setvar can unify with Class variable (Setvar ⊆ Class)
        // but the binding goes the right direction
        let factory = TestTermFactory;
        let vars = MetaByteFactory();

        let var_setvar = vars
            .list_metavariables_by_type(&SimpleType::Setvar)
            .next()
            .unwrap();
        let var_class = vars
            .list_metavariables_by_type(&SimpleType::Class)
            .next()
            .unwrap();

        let term_setvar = TestTerm::Leaf(var_setvar);
        let term_class = TestTerm::Leaf(var_class);

        // Unifying should succeed by binding `class_var` → `setvar_term`
        let result = unify(&factory, &term_setvar, &term_class);
        assert!(
            result.is_ok(),
            "Setvar should unify with Class (Setvar ⊆ Class)"
        );

        let subst = result.unwrap();
        // The class variable should be bound to the `setvar` term
        assert!(
            subst.contains(&var_class),
            "Class variable should be in substitution"
        );
        assert_eq!(subst.get(&var_class), Some(&term_setvar));
    }

    // =========================================================================
    // Pathological Mock Term Tests
    // =========================================================================

    /// A malformed term that violates the Term trait invariants.
    ///
    /// This term returns `None` for both `get_metavariable()` and `get_node()`,
    /// which should never happen for well-formed terms like `EnumTerm`.
    /// This is used to test defensive error handling.
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct PathologicalTerm;

    impl std::fmt::Display for PathologicalTerm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            std::fmt::Debug::fmt(&self, f)
        }
    }

    impl Term<SimpleType, MetaByte, NodeByte> for PathologicalTerm {
        type Type = SimpleType;
        type Metavariable = MetaByte;
        type Node = NodeByte;

        fn is_valid_sentence(&self) -> Result<bool, MguError> {
            Ok(false) // Deliberately invalid
        }

        fn get_type(&self) -> Result<SimpleType, MguError> {
            Ok(SimpleType::Boolean)
        }

        fn is_metavariable(&self) -> bool {
            false // Lies: claims not to be a metavariable
        }

        fn get_metavariable(&self) -> Option<MetaByte> {
            None // But returns None for metavariable
        }

        fn collect_metavariables(
            &self,
            _vars: &mut std::collections::HashSet<MetaByte>,
        ) -> Result<(), MguError> {
            Ok(())
        }

        fn get_node(&self) -> Option<NodeByte> {
            None // ALSO returns None for node - violates invariant!
        }

        fn get_n_children(&self) -> usize {
            0
        }

        fn get_child(&self, _index: usize) -> Option<&Self> {
            None
        }

        fn get_children(&self) -> impl Iterator<Item = &Self> {
            std::iter::empty()
        }

        fn get_children_as_slice(&self) -> &[Self] {
            &[]
        }

        fn format_with(&self, _formatter: &dyn crate::formatter::OutputFormatter) -> String {
            "PathologicalTerm".to_string()
        }
    }

    /// Factory for creating pathological terms (always returns the singleton).
    #[derive(Debug)]
    struct PathologicalFactory;

    impl TermFactory<PathologicalTerm, SimpleType, MetaByte, NodeByte> for PathologicalFactory {
        type TermType = SimpleType;
        type Term = PathologicalTerm;
        type TermNode = NodeByte;
        type TermMetavariable = MetaByte;

        fn from_factories<VF, NF>(_vars: VF, _nodes: NF) -> Self
        where
            VF: MetavariableFactory<Metavariable = MetaByte>,
            NF: NodeFactory<Node = NodeByte>,
        {
            PathologicalFactory
        }

        fn create_leaf(&self, _var: MetaByte) -> Result<PathologicalTerm, MguError> {
            Ok(PathologicalTerm) // Ignores the variable!
        }

        fn create_node(
            &self,
            _node: NodeByte,
            _children: Vec<PathologicalTerm>,
        ) -> Result<PathologicalTerm, MguError> {
            Ok(PathologicalTerm) // Ignores everything!
        }
    }

    #[test]
    fn pathological_term_triggers_defensive_error() {
        // This test verifies that the defensive error at lines 444-446
        // can be triggered by a malformed Term implementation.
        //
        // For EnumTerm, this error is UNREACHABLE by construction because:
        // - EnumTerm::Leaf always has `get_metavariable`() = Some(...)
        // - EnumTerm::`NodeOrLeaf` always has `get_node`() = Some(...)
        //
        // But a pathological Term could violate this invariant.

        let factory = PathologicalFactory;
        let subst = Substitution::<MetaByte, PathologicalTerm>::new();
        let pathological = PathologicalTerm;

        // Attempting to apply substitution to a pathological term should fail
        // with the defensive error "Non-metavariable term has no node"
        let result = apply_substitution(&factory, &subst, &pathological);

        assert!(result.is_err(), "Should fail for pathological term");

        let err = result.unwrap_err();
        let err_msg = format!("{}", err);
        assert!(
            err_msg.contains("Non-metavariable term has no node"),
            "Error message should be 'Non-metavariable term has no node', got: {}",
            err_msg
        );
    }
}
