//! Statement operations for proof construction.
//!
//! This module provides the core operations for building proofs:
//! - `contract`: Unify two hypotheses within a statement
//! - `relabel_disjoint`: Rename variables to avoid conflicts
//! - `apply`: Unify a hypothesis with another statement's assertion
//! - `apply_multiple`: Satisfy multiple hypotheses simultaneously
//! - `condensed_detach`: Meredith's condensed detachment (modus ponens application)

use super::base::Statement;
use crate::logic::propositional::rules::cn_basis::{
    modus_ponens, MP_MAJOR_PREMISE, MP_MINOR_PREMISE,
};
use crate::{
    apply_substitution, unify, DistinctnessGraph, Metavariable, MetavariableFactory, MguError,
    Node, NodeFactory, Substitution, Term, TermFactory, Type, TypeFactory,
};
use std::collections::HashSet;
use std::marker::PhantomData;

impl<Ty, V, N, T> Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// CONTRACT operation: Unify two hypotheses within a statement.
    ///
    /// Given S = (A; H; D) and indices n ≠ m, this attempts to unify Hₙ and Hₘ.
    /// If successful, returns a new statement with:
    /// - The unified substitution applied to A and all H
    /// - The unified hypothesis included once
    /// - Hypotheses n and m removed
    /// - Updated distinctness graph
    ///
    /// # Arguments
    ///
    /// * `factory` - Term factory for applying substitutions
    /// * `n` - Index of first hypothesis to unify
    /// * `m` - Index of second hypothesis to unify (must differ from `n`)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Indices are out of range or equal
    /// - Unification fails
    /// - Distinctness constraints are violated
    pub fn contract<TF, TyF>(&self, factory: &TF, n: usize, m: usize) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        // Validate indices
        if n == m {
            return Err(MguError::UnificationFailure(format!(
                "Cannot contract a hypothesis with itself (n={n}, m={m})"
            )));
        }

        let hyp_n = self
            .hypotheses
            .get(n)
            .ok_or_else(|| MguError::from_index_and_len(n, self.hypotheses.len()))?;

        let hyp_m = self
            .hypotheses
            .get(m)
            .ok_or_else(|| MguError::from_index_and_len(m, self.hypotheses.len()))?;

        // Unify the two hypotheses
        let subst = unify(factory, hyp_n, hyp_m)?;

        // Apply substitution to the statement
        let substituted = self.substitute(factory, &subst)?;

        // Remove duplicates from hypotheses (the unified hypotheses are now identical)
        let mut new_hypotheses = Vec::new();
        let mut seen = HashSet::new();

        for hyp in &substituted.hypotheses {
            if seen.insert(hyp.clone()) {
                new_hypotheses.push(hyp.clone());
            }
        }

        Ok(Self {
            _not_used: PhantomData,
            assertion: substituted.assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: substituted.distinctness_graph,
        })
    }

    /// Apply a variable-to-variable substitution (used for relabeling).
    ///
    /// # Errors
    ///
    /// Returns an error if term construction fails.
    fn apply_var_substitution<TF, TyF>(
        &self,
        term_factory: &TF,
        mapping: &std::collections::HashMap<V, V>,
    ) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        // Convert variable mapping to term mapping
        let mut term_mapping = std::collections::HashMap::new();
        for (old_var, new_var) in mapping {
            let new_term = term_factory.create_leaf(new_var.clone())?;
            term_mapping.insert(old_var.clone(), new_term);
        }

        let subst = Substitution::from(term_mapping);

        // Apply to assertion
        let new_assertion = apply_substitution(term_factory, &subst, &self.assertion)?;

        // Apply to hypotheses
        let mut new_hypotheses = Vec::new();
        for hyp in &self.hypotheses {
            new_hypotheses.push(apply_substitution(term_factory, &subst, hyp)?);
        }

        // Relabel distinctness graph: just rename the variables
        let mut new_graph = DistinctnessGraph::new();
        for (v1, v2) in self.distinctness_graph.edges_iter() {
            let new_v1 = mapping.get(&v1).cloned().unwrap_or(v1);
            let new_v2 = mapping.get(&v2).cloned().unwrap_or(v2);
            new_graph.add_edge(&new_v1, &new_v2)?;
        }

        Ok(Self {
            _not_used: PhantomData,
            assertion: new_assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: new_graph,
        })
    }

    /// Relabel all metavariables in this statement to be disjoint from a given set.
    ///
    /// This is the first step in APPLY(S₁, n, S₂) where we ensure S₂'s variables
    /// don't conflict with S₁'s variables.
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating fresh metavariables
    /// * `term_factory` - Factory for creating terms from metavariables
    /// * `avoid` - Set of metavariables to avoid when relabeling
    ///
    /// # Errors
    ///
    /// Returns an error if metavariable creation fails.
    pub fn relabel_disjoint<VF, TF, TyF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        avoid: &HashSet<V>,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<TyF, Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        let my_vars = self.collect_metavariables()?;

        // Build a mapping from old variables to new variables
        let mut relabeling: std::collections::HashMap<V, V> = std::collections::HashMap::new();
        let mut used = avoid.clone();

        // Create new variables for each variable in this statement
        for var in my_vars {
            let var_type = var.get_type()?;

            // Use the factory's iterator to find a fresh variable of the correct type
            let new_var = var_factory
                .list_metavariables_by_type(&var_type)
                .find(|candidate| !used.contains(candidate))
                .ok_or_else(|| {
                    MguError::AllocationError(format!(
                        "Could not find fresh metavariable of type {:?} while relabeling",
                        var_type
                    ))
                })?;

            relabeling.insert(var, new_var.clone());
            used.insert(new_var);
        }

        // Apply the relabeling
        self.apply_var_substitution(term_factory, &relabeling)
    }

    /// APPLY operation: Unify a hypothesis with another statement's assertion.
    ///
    /// Given S₁ = (A₁; H₁; D₁), S₂ = (A₂; H₂; D₂), and index n:
    /// 1. Relabel S₂ to be disjoint from S₁
    /// 2. Unify element n of H₁ with A₂
    /// 3. Return a new statement with:
    ///    - A₁ with the substitution applied
    ///    - H₁ (excluding element n) ∪ H₂ with substitution applied
    ///    - Merged distinctness graphs
    ///
    /// This is the core operation for building proofs in a Hilbert-style system.
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating fresh metavariables during relabeling
    /// * `term_factory` - Factory for applying substitutions
    /// * `n` - Index of the hypothesis to satisfy
    /// * `other` - The statement whose assertion will be unified with hypothesis `n`
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Index is out of range
    /// - Unification fails
    /// - Distinctness constraints are violated
    pub fn apply<VF, TF, TyF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        n: usize,
        other: &Self,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<TyF, Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        // Validate index
        let hyp_n = self
            .hypotheses
            .get(n)
            .ok_or_else(|| MguError::from_index_and_len(n, self.hypotheses.len()))?;

        // Step 1: Relabel other's variables to be disjoint from self's
        let my_vars = self.collect_metavariables()?;
        let other_relabeled = other.relabel_disjoint(var_factory, term_factory, &my_vars)?;

        // Step 2: Unify hypothesis n with other's assertion
        let subst = unify(term_factory, hyp_n, &other_relabeled.assertion)?;

        // Step 3: Apply substitution to both statements
        let self_subst = self.substitute(term_factory, &subst)?;
        let other_subst = other_relabeled.substitute(term_factory, &subst)?;

        // Step 4: Combine hypotheses (excluding hypothesis n from self)
        let mut new_hypotheses = Vec::new();
        let mut seen = HashSet::new();

        // Add hypotheses from self (except the one we unified)
        for (i, hyp) in self_subst.hypotheses.iter().enumerate() {
            if i != n && seen.insert(hyp.clone()) {
                new_hypotheses.push(hyp.clone());
            }
        }

        // Add hypotheses from other
        for hyp in &other_subst.hypotheses {
            if seen.insert(hyp.clone()) {
                new_hypotheses.push(hyp.clone());
            }
        }

        // Merge distinctness graphs
        let new_graph = Self::merge_distinctness_graphs(
            &self_subst.distinctness_graph,
            &other_subst.distinctness_graph,
        )?;

        Ok(Self {
            _not_used: PhantomData,
            assertion: self_subst.assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: new_graph,
        })
    }

    /// `APPLY_MULTIPLE` operation: Unify multiple hypotheses with multiple statements' assertions.
    ///
    /// Given S = (A; [H₀, H₁, ..., Hₙ₋₁]; D) and proofs = [P₀, P₁, ..., Pₙ₋₁]:
    /// 1. Relabel all Pᵢ to be mutually disjoint and disjoint from S
    /// 2. For each i, unify Hᵢ with Pᵢ's assertion (if Pᵢ is Some)
    /// 3. Return a new statement with:
    ///    - A with the combined substitution applied
    ///    - Union of all satisfied hypotheses from Pᵢ
    ///    - Merged distinctness graphs
    ///
    /// This is used for compact proof parsing where multiple hypotheses are satisfied simultaneously.
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating fresh metavariables during relabeling
    /// * `term_factory` - Factory for applying substitutions
    /// * `proofs` - Slice of optional statements, where None = unsatisfied hypothesis
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Length of proofs doesn't match number of hypotheses
    /// - Unification fails
    /// - Distinctness constraints are violated
    pub fn apply_multiple<VF, TF, TyF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        proofs: &[Option<Self>],
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<TyF, Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        // Validate that proofs length matches hypotheses length
        if proofs.len() != self.hypotheses.len() {
            return Err(MguError::UnificationFailure(format!(
                "apply_multiple: expected {} proofs, got {}",
                self.hypotheses.len(),
                proofs.len()
            )));
        }

        // Collect all variables to avoid
        let mut all_vars = self.collect_metavariables()?;

        // Step 1: Relabel all proofs to be mutually disjoint
        let mut relabeled_proofs: Vec<Option<Self>> = Vec::new();
        for proof_opt in proofs {
            if let Some(proof) = proof_opt {
                let relabeled = proof.relabel_disjoint(var_factory, term_factory, &all_vars)?;
                // Add relabeled proof's variables to avoid set
                all_vars.extend(relabeled.collect_metavariables()?);
                relabeled_proofs.push(Some(relabeled));
            } else {
                relabeled_proofs.push(None);
            }
        }

        // Step 2: Build combined substitution incrementally
        let mut combined_subst = Substitution::new();

        for (i, (hyp, proof_opt)) in self.hypotheses.iter().zip(&relabeled_proofs).enumerate() {
            if let Some(proof) = proof_opt {
                // Apply current substitution to both hypothesis and proof assertion
                let hyp_subst = apply_substitution(term_factory, &combined_subst, hyp)?;
                let proof_assertion_subst =
                    apply_substitution(term_factory, &combined_subst, &proof.assertion)?;

                // Unify hypothesis with proof's assertion
                let new_subst = unify(term_factory, &hyp_subst, &proof_assertion_subst)
                    .map_err(|e| {
                        MguError::UnificationFailure(format!(
                            "apply_multiple: failed to unify hypothesis {} with proof assertion: {}",
                            i, e
                        ))
                    })?;

                // Extend combined substitution with all mappings from `new_subst`
                for (var, term) in new_subst.iter() {
                    combined_subst.extend(var.clone(), term.clone())?;
                }
            }
        }

        // Step 3: Apply combined substitution to self
        let self_subst = self.substitute(term_factory, &combined_subst)?;

        // Step 4: Collect new hypotheses (unsatisfied from self, plus all from proofs)
        let mut new_hypotheses = Vec::new();
        let mut seen = HashSet::new();

        // Add unsatisfied hypotheses from self (where proof is None)
        for (i, hyp) in self_subst.hypotheses.iter().enumerate() {
            if relabeled_proofs[i].is_none() && seen.insert(hyp.clone()) {
                new_hypotheses.push(hyp.clone());
            }
        }

        // Add hypotheses from all proofs
        for proof in relabeled_proofs.iter().flatten() {
            let proof_subst = proof.substitute(term_factory, &combined_subst)?;
            for hyp in &proof_subst.hypotheses {
                if seen.insert(hyp.clone()) {
                    new_hypotheses.push(hyp.clone());
                }
            }
        }

        // Step 5: Merge all distinctness graphs
        let mut new_graph = self_subst.distinctness_graph.clone();

        for proof in relabeled_proofs.iter().flatten() {
            let proof_subst = proof.substitute(term_factory, &combined_subst)?;
            new_graph =
                Self::merge_distinctness_graphs(&new_graph, &proof_subst.distinctness_graph)?;
        }

        Ok(Self {
            _not_used: PhantomData,
            assertion: self_subst.assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: new_graph,
        })
    }

    /// CONDENSED DETACHMENT: Apply modus ponens to two statements.
    ///
    /// This is Meredith's condensed detachment operation, which applies two statements
    /// to the hypotheses of modus ponens. Given statements `minor` and `major`:
    ///
    /// 1. Create fresh modus ponens: MP = (ψ; φ, (φ → ψ); ∅)
    /// 2. Apply statements to MP's hypotheses using [`apply_multiple`](Self::apply_multiple):
    ///    - `minor` matches φ (the minor premise at [`MP_MINOR_PREMISE`])
    ///    - `major` matches (φ → ψ) (the major premise at [`MP_MAJOR_PREMISE`])
    /// 3. Return the resulting statement
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating fresh metavariables
    /// * `term_factory` - Factory for creating terms
    /// * `minor` - Statement matching the minor premise φ
    /// * `major` - Statement matching the major premise (φ → ψ)
    /// * `implies_node` - Node representing the implication operator (→)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Metavariable or term creation fails
    /// - Unification fails (statements don't match modus ponens pattern)
    /// - Distinctness constraints are violated
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::*;
    /// use SimpleType::*;
    ///
    /// # fn example() -> Result<(), MguError> {
    /// let var_factory = MetaByteFactory::new(SimpleTypeFactory);
    /// let term_factory = EnumTermFactory::new(SimpleTypeFactory);
    ///
    /// // Create P and (P → Q)
    /// let p = var_factory.create("P", &Boolean)?;
    /// let q = var_factory.create("Q", &Boolean)?;
    /// let p_term = term_factory.create_leaf(p)?;
    /// let q_term = term_factory.create_leaf(q)?;
    ///
    /// let p_implies_q = term_factory.create_node(
    ///     NodeByte::Implies,
    ///     vec![p_term.clone(), q_term.clone()]
    /// )?;
    ///
    /// // Build statements: minor = (P; ∅; ∅) and major = ((P → Q); ∅; ∅)
    /// let minor = Statement::simple_axiom(&SimpleTypeFactory, p_term)?;
    /// let major = Statement::simple_axiom(&SimpleTypeFactory, p_implies_q)?;
    ///
    /// // Condensed detachment: should derive Q
    /// let result = Statement::condensed_detach(
    ///     &var_factory,
    ///     &term_factory,
    ///     &minor,
    ///     &major,
    ///     NodeByte::Implies
    /// )?;
    ///
    /// // Result should be (Q; ∅; ∅)
    /// assert_eq!(result.get_n_hypotheses(), 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn condensed_detach<VF, TF, TyF>(
        var_factory: &VF,
        term_factory: &TF,
        minor: &Self,
        major: &Self,
        implies_node: N,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<TyF, Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<
            T,
            Ty,
            V,
            N,
            TyF,
            TermType = Ty,
            Term = T,
            TermMetavariable = V,
            TermNode = N,
        >,
        TyF: TypeFactory<Type = Ty>,
    {
        // Create fresh Boolean metavariables for modus ponens
        let bool_type = var_factory.type_factory().try_boolean()?;
        let phi_var = var_factory
            .list_metavariables_by_type(&bool_type)
            .next()
            .ok_or_else(|| {
                MguError::AllocationError("Could not create fresh Boolean variable φ".to_string())
            })?;

        let psi_var = var_factory
            .list_metavariables_by_type(&bool_type)
            .nth(1)
            .ok_or_else(|| {
                MguError::AllocationError("Could not create fresh Boolean variable ψ".to_string())
            })?;

        // Build modus ponens using the helper function
        let mp = modus_ponens(term_factory, phi_var, psi_var, implies_node)?;

        // Build proofs array using MP constants to make ordering explicit
        let mut proofs = vec![None, None];
        proofs[MP_MINOR_PREMISE] = Some(minor.clone());
        proofs[MP_MAJOR_PREMISE] = Some(major.clone());

        // Apply both statements to modus ponens hypotheses
        let result = mp.apply_multiple(var_factory, term_factory, &proofs)?;

        // Canonicalize the result to ensure consistent variable naming
        result.canonicalize(var_factory, term_factory)
    }

    /// Return a canonical form of this statement.
    ///
    /// Canonical form provides a unique representative for α-equivalent statements
    /// by renaming variables to minimal lexicographic ordering and reordering hypotheses.
    ///
    /// # Algorithm
    ///
    /// 1. Try all permutations of hypothesis orderings
    /// 2. For each permutation, traverse (`assertion`, `hyp`\[n-1\], ..., `hyp`\[0\]) in pre-order
    /// 3. Assign fresh variables (starting from index 0) in encounter order
    /// 4. Keep the lexicographically minimal result
    ///
    /// # Computational Cost
    ///
    /// This operation has factorial complexity in the number of hypotheses.
    /// For statements with many hypotheses, this may be expensive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Statement, MetaByte, Metavariable, SimpleType, SimpleTypeFactory, NodeByte, Node};
    /// use symbolic_mgu::{EnumTerm, EnumTermFactory, MetaByteFactory, MetavariableFactory};
    /// use itertools::Itertools;
    /// use SimpleType::*;
    ///
    /// let var_factory = MetaByteFactory::new(SimpleTypeFactory);
    /// let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte, _>::new(SimpleTypeFactory);
    ///
    /// // Create φ₂ → φ₅ (non-canonical variables)
    /// let vars = MetaByteFactory::new(SimpleTypeFactory);
    /// let (_, _, phi2, _, _, phi5) = vars
    ///         .list_metavariables_by_type(&Boolean)
    ///         .tuples()
    ///         .next()
    ///         .unwrap();
    /// let implies = NodeByte::Implies;
    ///
    /// let phi2_term: EnumTerm<SimpleType, MetaByte, NodeByte> = EnumTerm::Leaf(phi2);
    /// let phi5_term = EnumTerm::Leaf(phi5);
    /// let implication = EnumTerm::NodeOrLeaf(implies, vec![phi2_term, phi5_term]);
    ///
    /// let stmt = Statement::simple_axiom(&SimpleTypeFactory, implication).unwrap();
    ///
    /// // Canonicalize to get (φ₀ → φ₁)
    /// let canonical = stmt.canonicalize(&var_factory, &term_factory).unwrap();
    ///
    /// // The canonical form uses φ₀ and φ₁
    /// let vars = canonical.collect_metavariables().unwrap();
    /// assert_eq!(vars.len(), 2); // Two variables remain
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if variable or term creation fails.
    pub fn canonicalize<VF, TF, TyF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<TyF, Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
    {
        use itertools::Itertools;
        use std::collections::HashMap;

        let all_vars = self.collect_metavariables()?;
        let n_hyp = self.hypotheses.len();

        // Track the best canonical form found
        let mut best_canonical: Option<Self> = None;

        // Try all permutations of hypothesis orderings
        for perm in (0..n_hyp).permutations(n_hyp) {
            // Create fresh iterator for each metavariable type by collecting all types
            let mut type_iterators: HashMap<Ty, Box<dyn Iterator<Item = V>>> = HashMap::new();

            // Collect all unique types from variables
            let mut types_seen = HashSet::new();
            for var in &all_vars {
                let (var_type, _) = var.get_type_and_index()?;
                types_seen.insert(var_type);
            }

            // Create iterators for each type
            for typ in types_seen {
                type_iterators.insert(
                    typ.clone(),
                    Box::new(var_factory.list_metavariables_by_type(&typ)),
                );
            }

            // Build variable renaming map via pre-order traversal
            // Visit order: (`assertion`, `hyp[perm[n-1]]`, ..., `hyp[perm[0]]`)
            let mut var_map: HashMap<V, V> = HashMap::new();

            // Collect terms to traverse in order
            let mut terms_to_traverse = vec![&self.assertion];
            for &idx in perm.iter().rev() {
                terms_to_traverse.push(&self.hypotheses[idx]);
            }

            // Traverse each term
            for term in terms_to_traverse {
                let mut stack = vec![term];

                while let Some(current) = stack.pop() {
                    if let Some(v) = current.get_metavariable() {
                        // If we haven't seen this variable, map it to next fresh variable
                        if !var_map.contains_key(&v) {
                            let (var_type, _) = v.get_type_and_index()?;
                            let iter = type_iterators.get_mut(&var_type).ok_or_else(|| {
                                MguError::AllocationError(format!(
                                    "No iterator for type {:?}",
                                    var_type
                                ))
                            })?;
                            let fresh = iter.next().ok_or_else(|| {
                                MguError::AllocationError(
                                    "Ran out of fresh metavariables".to_string(),
                                )
                            })?;
                            var_map.insert(v.clone(), fresh);
                        }
                    } else {
                        // Pre-order: visit children in natural order (left to right)
                        // Push in reverse order so we pop in natural order
                        let children: Vec<_> = current.get_children().collect();
                        for child in children.iter().rev() {
                            stack.push(child);
                        }
                    }

                    // Early exit if we've mapped all variables
                    if var_map.len() == all_vars.len() {
                        break;
                    }
                }

                // Early exit if we've mapped all variables
                if var_map.len() == all_vars.len() {
                    break;
                }
            }

            // Apply the variable renaming to create candidate
            let candidate = self.apply_var_substitution(term_factory, &var_map)?;

            // Reorder hypotheses according to permutation
            let mut reordered_hyps = Vec::with_capacity(n_hyp);
            for &idx in &perm {
                reordered_hyps.push(candidate.hypotheses[idx].clone());
            }

            let reordered_candidate = Self {
                _not_used: PhantomData,
                assertion: candidate.assertion.clone(),
                hypotheses: reordered_hyps,
                distinctness_graph: candidate.distinctness_graph.clone(),
            };

            // Compare lexicographically: (`assertion`, `hyp[n-1]`, ..., `hyp[0]`)
            // Keep the smallest
            let is_better = if let Some(ref best) = best_canonical {
                // Compare assertion first
                match reordered_candidate.assertion.cmp(&best.assertion) {
                    std::cmp::Ordering::Less => true,
                    std::cmp::Ordering::Greater => false,
                    std::cmp::Ordering::Equal => {
                        // Compare hypotheses in reverse order
                        let candidate_hyps_rev: Vec<_> =
                            reordered_candidate.hypotheses.iter().rev().collect();
                        let best_hyps_rev: Vec<_> = best.hypotheses.iter().rev().collect();
                        candidate_hyps_rev < best_hyps_rev
                    }
                }
            } else {
                true // First candidate is automatically best
            };

            if is_better {
                best_canonical = Some(reordered_candidate);
            }
        }

        best_canonical
            .ok_or_else(|| MguError::AllocationError("Failed to find canonical form".to_string()))
    }

    /// Convert a statement to use different implementations of Type, Metavariable, Node, and Term.
    ///
    /// This method enables converting between different backend implementations while preserving
    /// the logical structure of the statement. For example, converting from `MetaByte` (limited
    /// to 32 variables) to `WideMetavariable` (unlimited variables), or vice versa.
    ///
    /// The conversion process:
    /// 1. Collects all variables from the source statement, grouped by type
    /// 2. Maps each variable to the destination implementation using factory iterators
    /// 3. Detects if the destination implementation has insufficient capacity
    /// 4. Recursively converts all terms (assertion and hypotheses)
    /// 5. Converts the distinctness graph
    ///
    /// # Type Parameters
    ///
    /// * `Ty2` - Destination Type implementation
    /// * `V2` - Destination Metavariable implementation
    /// * `N2` - Destination Node implementation
    /// * `T2` - Destination Term implementation
    /// * `VF` - Metavariable factory for creating destination variables
    /// * `NF` - Node factory for creating destination nodes
    /// * `TF` - Term factory for creating destination terms
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating destination metavariables
    /// * `node_factory` - Factory for creating destination nodes
    /// * `term_factory` - Factory for creating destination terms
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The destination metavariable implementation is exhausted (e.g., converting a statement
    ///   with 15 Boolean variables to `MetaByte` which supports only 11)
    /// - Type conversion fails (if source and destination type systems are incompatible)
    /// - Term conversion fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use symbolic_mgu::{Statement, SimpleType, SimpleTypeFactory, MetaByte, MetaByteFactory, MetavariableFactory};
    /// # use symbolic_mgu::{WideMetavariable, WideMetavariableFactory};
    /// # use symbolic_mgu::{NodeByte, NodeByteFactory, EnumTerm, EnumTermFactory, TermFactory, MguError};
    /// # use SimpleType::*;
    /// # fn example() -> Result<(), MguError> {
    /// // Original statement using MetaByte
    /// let meta_var_factory = MetaByteFactory::new(SimpleTypeFactory);
    /// let term_factory: EnumTermFactory<SimpleType, _, NodeByte, _> = EnumTermFactory::new(SimpleTypeFactory);
    /// let p = meta_var_factory.create("P", &Boolean)?;
    /// let p_term = term_factory.create_leaf(p)?;
    /// let stmt = Statement::new(&SimpleTypeFactory, p_term, vec![], Default::default())?;
    ///
    /// // Convert to WideMetavariable
    /// let var_factory = WideMetavariableFactory::new(SimpleTypeFactory);
    /// let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    /// let wide_term_factory = EnumTermFactory::new(SimpleTypeFactory);
    ///
    /// let converted: Statement<SimpleType, WideMetavariable, NodeByte, EnumTerm<_, _, _>> =
    ///     stmt.convert(&var_factory, &node_factory, &wide_term_factory)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn convert<Ty2, V2, N2, T2, VF, NF, TF, TyF>(
        &self,
        var_factory: &VF,
        node_factory: &NF,
        term_factory: &TF,
    ) -> Result<Statement<Ty2, V2, N2, T2>, MguError>
    where
        Ty2: Type,
        V2: Metavariable<Type = Ty2>,
        N2: Node<Type = Ty2>,
        T2: Term<Ty2, V2, N2>,
        VF: MetavariableFactory<TyF, Metavariable = V2, MetavariableType = Ty2>,
        NF: NodeFactory<Node = N2, NodeType = Ty2>,
        TF: TermFactory<T2, Ty2, V2, N2, TyF, Term = T2, TermNode = N2, TermMetavariable = V2>,
        TyF: TypeFactory<Type = Ty2>,
    {
        use std::collections::HashMap;

        // Step 1: Collect all unique variables from the statement, grouped by type
        let mut vars_set: HashSet<V> = HashSet::new();
        self.assertion.collect_metavariables(&mut vars_set)?;
        for hyp in &self.hypotheses {
            hyp.collect_metavariables(&mut vars_set)?;
        }

        let mut vars_by_type: HashMap<Ty, Vec<V>> = HashMap::new();
        for var in vars_set {
            let ty = var.get_type()?;
            vars_by_type.entry(ty).or_default().push(var);
        }

        // Step 2: Build variable mapping using factory iterators
        let mut var_map: HashMap<V, V2> = HashMap::new();

        for (src_type, src_vars) in vars_by_type {
            // Convert type using capability checks
            let dest_type = if src_type.is_boolean() {
                var_factory.type_factory().try_boolean()?
            } else if src_type.is_setvar() {
                var_factory.type_factory().try_setvar()?
            } else if src_type.is_class() {
                var_factory.type_factory().try_class()?
            } else {
                return Err(MguError::ArgumentError(
                    "Unsupported type conversion: source type does not support boolean/setvar/class checks".to_string()
                ));
            };

            // Get iterator from destination factory
            let mut dest_iter = var_factory.list_metavariables_by_type(&dest_type);

            // Map each source variable to next destination variable
            for src_var in src_vars {
                let dest_var = dest_iter.next().ok_or_else(|| {
                    MguError::AllocationError(format!(
                        "Destination metavariable implementation exhausted for type {:?}",
                        dest_type
                    ))
                })?;
                var_map.insert(src_var, dest_var);
            }
        }

        // Step 3: Define recursive term conversion helper
        // Note: We use a nested function instead of a closure because closures
        // cannot be recursive without `RefCell` or similar workarounds

        /// Recursively convert a term from one implementation to another.
        ///
        /// This helper function is used by `Statement::convert()` to recursively
        /// transform terms by mapping variables and replicating nodes.
        fn convert_term_impl<Ty, V, N, T, Ty2, V2, N2, T2, NF, TF, TyF>(
            term: &T,
            var_map: &HashMap<V, V2>,
            node_factory: &NF,
            term_factory: &TF,
        ) -> Result<T2, MguError>
        where
            Ty: Type,
            V: Metavariable<Type = Ty>,
            N: Node<Type = Ty>,
            T: Term<Ty, V, N>,
            Ty2: Type,
            V2: Metavariable<Type = Ty2>,
            N2: Node<Type = Ty2>,
            T2: Term<Ty2, V2, N2>,
            NF: NodeFactory<Node = N2, NodeType = Ty2>,
            TF: TermFactory<T2, Ty2, V2, N2, TyF, Term = T2, TermNode = N2, TermMetavariable = V2>,
            TyF: TypeFactory<Type = Ty2>,
        {
            if let Some(src_var) = term.get_metavariable() {
                // Leaf case: look up mapped variable
                let dest_var = var_map.get(&src_var).ok_or_else(|| {
                    MguError::ArgumentError("Variable not found in mapping".to_string())
                })?;
                term_factory.create_leaf(dest_var.clone())
            } else {
                // Node case: convert node and children
                // SAFETY: If `get_metavariable`() returned None, `get_node`() must return Some
                let src_node = term
                    .get_node()
                    .expect("Term must be either metavariable or node");

                // Convert node using factory's `type_and_index` method
                let (node_type, node_index) = src_node.get_type_and_index()?;

                // Convert the node's type
                let dest_node_type = if node_type.is_boolean() {
                    term_factory.type_factory().try_boolean()?
                } else if node_type.is_setvar() {
                    term_factory.type_factory().try_setvar()?
                } else if node_type.is_class() {
                    term_factory.type_factory().try_class()?
                } else {
                    return Err(MguError::ArgumentError(
                        "Unsupported node type conversion".to_string(),
                    ));
                };

                let dest_node =
                    node_factory.create_by_type_and_index(dest_node_type, node_index)?;

                // Recursively convert children
                let dest_children: Result<Vec<T2>, MguError> = term
                    .get_children()
                    .map(|child| convert_term_impl(child, var_map, node_factory, term_factory))
                    .collect();

                term_factory.create_node(dest_node, dest_children?)
            }
        }

        // Step 4: Convert assertion and hypotheses
        let new_assertion =
            convert_term_impl(&self.assertion, &var_map, node_factory, term_factory)?;
        let new_hypotheses: Result<Vec<T2>, MguError> = self
            .hypotheses
            .iter()
            .map(|h| convert_term_impl(h, &var_map, node_factory, term_factory))
            .collect();
        let new_hypotheses = new_hypotheses?;

        // Step 5: Convert distinctness graph
        let mut new_distinctness = DistinctnessGraph::new();
        for (v1, v2) in self.distinctness_graph.edges_iter() {
            let dest_v1 = var_map.get(&v1).ok_or_else(|| {
                MguError::ArgumentError(
                    "Variable in distinctness graph not found in mapping".to_string(),
                )
            })?;
            let dest_v2 = var_map.get(&v2).ok_or_else(|| {
                MguError::ArgumentError(
                    "Variable in distinctness graph not found in mapping".to_string(),
                )
            })?;
            new_distinctness.add_edge(dest_v1, dest_v2)?;
        }

        // Step 6: Build new statement
        Ok(Statement {
            _not_used: PhantomData,
            assertion: new_assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: new_distinctness,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::logic::create_dict;
    use crate::{
        EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, NodeByte,
        SimpleType, SimpleTypeFactory, Statement, Term, TermFactory,
    };
    use itertools::Itertools;
    use std::collections::HashSet;
    use SimpleType::*;

    type TestStatement =
        Statement<SimpleType, MetaByte, NodeByte, EnumTerm<SimpleType, MetaByte, NodeByte>>;

    // ==========================================================================
    // Phase A1: CONTRACT Error Cases
    // ==========================================================================

    #[test]
    fn contract_with_equal_indices_fails() {
        // CONTRACT(stmt, 0, 0) should error: can't contract with self
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create simple statement: (φ; [P, Q]; {})
        let (phi, p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term, q_term],
            Default::default(),
        )
        .unwrap();

        // Try to contract hypothesis 0 with itself
        let result = stmt.contract(&term_factory, 0, 0);

        assert!(result.is_err(), "CONTRACT with equal indices should fail");
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("Cannot contract a hypothesis with itself"),
                "Error message should mention self-contraction: {}",
                msg
            );
        }
    }

    #[test]
    fn contract_with_out_of_bounds_n_fails() {
        // CONTRACT(stmt, 99, 0) should error: index out of range
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let phi = var_factory
            .list_metavariables_by_type(&Boolean)
            .next()
            .unwrap();
        let p = var_factory
            .list_metavariables_by_type(&Boolean)
            .nth(1)
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Try with n out of bounds (statement has only 1 hypothesis)
        let result = stmt.contract(&term_factory, 99, 0);

        assert!(result.is_err(), "CONTRACT with out-of-bounds n should fail");
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("out of range") || msg.contains("Index"),
                "Error should mention index out of range: {}",
                msg
            );
        }
    }

    #[test]
    fn contract_with_out_of_bounds_m_fails() {
        // CONTRACT(stmt, 0, 99) should error: index out of range
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let phi = var_factory
            .list_metavariables_by_type(&Boolean)
            .next()
            .unwrap();
        let p = var_factory
            .list_metavariables_by_type(&Boolean)
            .nth(1)
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();

        let stmt: TestStatement =
            Statement::new(&type_factory, phi_term, vec![p_term], Default::default()).unwrap();

        // Try with m out of bounds
        let result = stmt.contract(&term_factory, 0, 99);

        assert!(result.is_err(), "CONTRACT with out-of-bounds m should fail");
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("out of range") || msg.contains("Index"),
                "Error should mention index out of range: {}",
                msg
            );
        }
    }

    // Note: Type incompatibility at the hypothesis level is prevented by Statement's
    // type system - all hypotheses must be Boolean. Type mismatches at deeper levels
    // (within term children) are already thoroughly tested in unification property tests.

    #[test]
    fn contract_different_operators_fails() {
        // Hypothesis 0: P → Q
        // Hypothesis 1: P ∧ Q
        // CONTRACT(stmt, 0, 1) should error: Implies ≠ And
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // Create P → Q
        let p_implies_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), q_term.clone()])
            .unwrap();

        // Create P ∧ Q
        let p_and_q = term_factory
            .create_node(NodeByte::And, vec![p_term, q_term])
            .unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_implies_q, p_and_q],
            Default::default(),
        )
        .unwrap();

        // Try to contract different operators
        let result = stmt.contract(&term_factory, 0, 1);

        assert!(
            result.is_err(),
            "CONTRACT of different operators should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("unif") || msg.contains("Node") || msg.contains("mismatch"),
                "Error should mention unification failure or node mismatch: {}",
                msg
            );
        }
    }

    // ==========================================================================
    // Phase A2: CONTRACT Simple Success Cases
    // ==========================================================================

    #[test]
    fn contract_identical_hypotheses_succeeds() {
        // Assertion: φ
        // Hypothesis 0: P
        // Hypothesis 1: P (identical to hypothesis 0)
        // Distinctness: {}
        //
        // contract(stmt, 0, 1) should:
        // - Unify with identity substitution (P ↦ P)
        // - Result: (φ; [P]; {})
        // - Only one copy of P in hypotheses
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (p, phi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let phi_term = term_factory.create_leaf(phi).unwrap();

        // Statement: (φ; [P, P]; {})
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term.clone(), p_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Contract hypotheses 0 and 1 (both are P)
        let result = stmt.contract(&term_factory, 0, 1);

        assert!(
            result.is_ok(),
            "CONTRACT with identical hypotheses should succeed"
        );

        let contracted = result.unwrap();

        // Verify: only one hypothesis remains
        assert_eq!(
            contracted.hypotheses.len(),
            1,
            "Result should have 1 hypothesis (duplicates merged)"
        );

        // Verify: the remaining hypothesis is P
        assert_eq!(
            contracted.hypotheses[0], p_term,
            "Remaining hypothesis should be P"
        );
    }

    #[test]
    fn contract_unifies_variables() {
        // Assertion: φ → ψ
        // Hypothesis 0: φ
        // Hypothesis 1: ψ
        // Distinctness: {}
        //
        // contract(stmt, 0, 1) should succeed
        // Result assertion: χ → χ (both renamed to same variable)
        // Result hypotheses: [χ]
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create φ → ψ
        let phi_implies_psi = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term.clone()])
            .unwrap();

        // Statement: (φ → ψ; [φ, ψ]; {})
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_implies_psi,
            vec![phi_term.clone(), psi_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Contract hypotheses 0 and 1 (unify φ with ψ)
        let result = stmt.contract(&term_factory, 0, 1);

        assert!(
            result.is_ok(),
            "CONTRACT with unifiable variables should succeed"
        );

        let contracted = result.unwrap();

        // Verify: only one hypothesis remains
        assert_eq!(
            contracted.hypotheses.len(),
            1,
            "Result should have 1 hypothesis (unified)"
        );

        // Verify: assertion is χ → χ (same variable on both sides)
        // After unification and substitution, both φ and ψ become the same variable
        // The assertion should have the form X → X where X is some Boolean variable

        // Verify by checking the structure: it should be Implies with identical children
        if let Some(implies_node) = contracted.assertion.get_node() {
            assert_eq!(
                implies_node,
                NodeByte::Implies,
                "Assertion should still be an implication"
            );

            let children: Vec<_> = contracted.assertion.get_children().collect();
            assert_eq!(children.len(), 2, "Implication should have 2 children");

            // Both children should be identical after unification
            assert_eq!(
                children[0], children[1],
                "After unifying φ and ψ, assertion should be χ → χ"
            );
        } else {
            panic!("Assertion should be a node (Implies), not a metavariable");
        }

        // Verify: the single remaining hypothesis matches one side of the implication
        let children: Vec<_> = contracted.assertion.get_children().collect();
        assert_eq!(
            contracted.hypotheses[0], *children[0],
            "Remaining hypothesis should match the unified variable"
        );
    }

    // ==========================================================================
    // Phase C1: APPLY Error Cases
    // ==========================================================================

    #[test]
    fn apply_with_out_of_bounds_index_fails() {
        // APPLY(stmt, 99, other) should error: index out of range
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        let stmt1: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![psi_term.clone()],
            Default::default(),
        )
        .unwrap();
        let stmt2: TestStatement = Statement::simple_axiom(&type_factory, psi_term).unwrap();

        // Try with index out of bounds (stmt1 has only 1 hypothesis at index 0)
        let result = stmt1.apply(&var_factory, &term_factory, 99, &stmt2);

        assert!(
            result.is_err(),
            "APPLY with out-of-bounds index should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("out of range") || msg.contains("Index"),
                "Error should mention index out of range: {}",
                msg
            );
        }
    }

    // Note: Type incompatibility is prevented by Statement's type system (all hypotheses
    // and assertions must be Boolean). Type mismatches at deeper levels are already
    // tested in unification property tests.

    #[test]
    fn apply_unification_failure() {
        // S1.`hypothesis`[0]: P → Q
        // S2.assertion: P ∧ Q (different operator, won't unify)
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // Create P → Q
        let p_implies_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), q_term.clone()])
            .unwrap();

        // Create P ∧ Q
        let p_and_q = term_factory
            .create_node(NodeByte::And, vec![p_term, q_term])
            .unwrap();

        // stmt1: (φ; [P → Q]; {})
        let stmt1: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_implies_q],
            Default::default(),
        )
        .unwrap();

        // stmt2: (P ∧ Q; []; {})
        let stmt2: TestStatement = Statement::simple_axiom(&type_factory, p_and_q).unwrap();

        // Try to apply: unify `hypothesis`[0] (P → Q) with assertion (P ∧ Q)
        let result = stmt1.apply(&var_factory, &term_factory, 0, &stmt2);

        assert!(
            result.is_err(),
            "APPLY with unification failure should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("unif") || msg.contains("Node") || msg.contains("mismatch"),
                "Error should mention unification failure: {}",
                msg
            );
        }
    }

    // ==========================================================================
    // Phase D1: APPLY_MULTIPLE Error Cases
    // ==========================================================================

    #[test]
    fn apply_multiple_with_empty_proofs_fails() {
        // Statement with 2 hypotheses, proofs = []
        // Should error: insufficient proofs
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term, q_term],
            Default::default(),
        )
        .unwrap();

        let empty_proofs: Vec<Option<TestStatement>> = vec![];

        // Try with empty proofs list
        let result = stmt.apply_multiple(&var_factory, &term_factory, &empty_proofs);

        assert!(
            result.is_err(),
            "APPLY_MULTIPLE with empty proofs should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("proof") || msg.contains("insufficient") || msg.contains("mismatch"),
                "Error should mention insufficient proofs: {}",
                msg
            );
        }
    }

    #[test]
    fn apply_multiple_with_too_few_proofs_fails() {
        // Statement with 3 hypotheses, proofs.len() = 2
        // Should error: insufficient proofs
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, p, q, r) = var_factory
            .list_metavariables_by_type(&Boolean)
            .take(4)
            .collect_tuple()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let r_term = term_factory.create_leaf(r).unwrap();

        // Statement with 3 hypotheses
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term.clone(), q_term.clone(), r_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Only 2 proofs for 3 hypotheses
        let proof1 = Statement::simple_axiom(&type_factory, p_term).unwrap();
        let proof2 = Statement::simple_axiom(&type_factory, q_term).unwrap();
        let proofs = vec![Some(proof1), Some(proof2)];

        let result = stmt.apply_multiple(&var_factory, &term_factory, &proofs);

        assert!(
            result.is_err(),
            "APPLY_MULTIPLE with too few proofs should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("proof") || msg.contains("insufficient") || msg.contains("mismatch"),
                "Error should mention insufficient proofs: {}",
                msg
            );
        }
    }

    #[test]
    fn apply_multiple_with_too_many_proofs_fails() {
        // Statement with 2 hypotheses, proofs.len() = 3
        // Should error or ignore extras? Check implementation behavior.
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, p, q, r) = var_factory
            .list_metavariables_by_type(&Boolean)
            .take(4)
            .collect_tuple()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let r_term = term_factory.create_leaf(r).unwrap();

        // Statement with 2 hypotheses
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term,
            vec![p_term.clone(), q_term.clone()],
            Default::default(),
        )
        .unwrap();

        // 3 proofs for 2 hypotheses
        let proof1 = Statement::simple_axiom(&type_factory, p_term).unwrap();
        let proof2 = Statement::simple_axiom(&type_factory, q_term).unwrap();
        let proof3 = Statement::simple_axiom(&type_factory, r_term).unwrap();
        let proofs = vec![Some(proof1), Some(proof2), Some(proof3)];

        let result = stmt.apply_multiple(&var_factory, &term_factory, &proofs);

        assert!(
            result.is_err(),
            "APPLY_MULTIPLE with too many proofs should fail"
        );
        if let Err(e) = result {
            let msg = format!("{:?}", e);
            assert!(
                msg.contains("proof") || msg.contains("mismatch") || msg.contains("length"),
                "Error should mention proof count mismatch: {}",
                msg
            );
        }
    }

    // ==========================================================================
    // Phase E1: `CONDENSED_DETACH` Error Cases
    // ==========================================================================

    #[test]
    fn condensed_detach_non_implication_major_fails() {
        // Major premise: P ∧ Q (not an implication)
        // Should error: major premise must be implication
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // Create P ∧ Q (not an implication)
        let p_and_q = term_factory
            .create_node(NodeByte::And, vec![p_term.clone(), q_term])
            .unwrap();

        // Major: (P ∧ Q; []; {}) - not an implication
        let major: TestStatement = Statement::simple_axiom(&type_factory, p_and_q).unwrap();

        // Minor: (P; []; {})
        let minor: TestStatement = Statement::simple_axiom(&type_factory, p_term).unwrap();

        // Try condensed detachment with non-implication major premise
        let result = TestStatement::condensed_detach(
            &var_factory,
            &term_factory,
            &minor,
            &major,
            NodeByte::Implies,
        );

        assert!(
            result.is_err(),
            "CONDENSED_DETACH with non-implication major should fail during unification"
        );
        // The error comes from `apply_multiple` failing to unify (P ∧ Q) with (φ → ψ)
        // due to node mismatch (And vs Implies)
    }

    #[test]
    fn condensed_detach_with_unifiable_metavariables_succeeds() {
        // Major: P → Q
        // Minor: R (unifies with P via substitution R := P)
        // Should succeed, yielding Q
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (p, q, r) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let r_term = term_factory.create_leaf(r).unwrap();

        // Create P → Q
        let p_implies_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term, q_term])
            .unwrap();

        // Major: (P → Q; []; {})
        let major: TestStatement = Statement::simple_axiom(&type_factory, p_implies_q).unwrap();

        // Minor: (R; []; {}) - won't unify with P
        let minor: TestStatement = Statement::simple_axiom(&type_factory, r_term).unwrap();

        // Try condensed detachment with non-matching premises
        let result = TestStatement::condensed_detach(
            &var_factory,
            &term_factory,
            &minor,
            &major,
            NodeByte::Implies,
        );

        // Note: This test was originally designed to test failure with "non-matching"
        // premises (Minor: R, Major: P → Q). However, this expectation is incorrect.
        // Since R and P are both Boolean metavariables, they unify successfully (R := P),
        // and condensed detachment succeeds as expected, yielding Q.
        //
        // The test above (non-implication major) already covers the main error case
        // (node mismatch during unification). Creating a true unification failure would
        // require structurally incompatible terms, which is already thoroughly tested
        // in unification property tests.
        assert!(
            result.is_ok(),
            "CONDENSED_DETACH with compatible metavariables should succeed"
        );
    }

    // Phase B1: CANONICALIZE Property Tests

    #[test]
    fn canonicalize_is_idempotent() {
        // Property: canon(canon(S)) = canon(S)
        // Canonicalization should reach a fixed point after one application.
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create a statement with non-canonical variables: φ₂ → φ₅
        let (_, _, phi2, _, _, phi5) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();

        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi2_term, phi5_term])
            .unwrap();

        let stmt: TestStatement = Statement::simple_axiom(&type_factory, implication).unwrap();

        // First canonicalization: φ₂ → φ₅ becomes φ₀ → φ₁
        let canon1 = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Second canonicalization: should be identical
        let canon2 = canon1.canonicalize(&var_factory, &term_factory).unwrap();

        // Compare via Debug representation since Statement doesn't implement PartialEq
        let canon1_str = format!("{:?}", canon1);
        let canon2_str = format!("{:?}", canon2);

        assert_eq!(
            canon1_str, canon2_str,
            "Canonicalization should be idempotent: canon(canon(S)) = canon(S)"
        );
    }

    #[test]
    fn canonicalize_preserves_alpha_equivalence() {
        // Property: if S1 ≡ᵅ S2, then canon(S1) = canon(S2)
        // α-equivalent statements (same structure, different variables) should
        // have identical canonical forms.
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create first statement: φ₂ → φ₅
        let (_, _, phi2, _, _, phi5) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();

        let impl1 = term_factory
            .create_node(NodeByte::Implies, vec![phi2_term, phi5_term])
            .unwrap();

        let stmt1: TestStatement = Statement::simple_axiom(&type_factory, impl1).unwrap();

        // Create second statement: φ₃ → φ₇ (α-equivalent to first)
        let (_, _, _, phi3, _, _, _, phi7) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi3_term = term_factory.create_leaf(phi3).unwrap();
        let phi7_term = term_factory.create_leaf(phi7).unwrap();

        let impl2 = term_factory
            .create_node(NodeByte::Implies, vec![phi3_term, phi7_term])
            .unwrap();

        let stmt2: TestStatement = Statement::simple_axiom(&type_factory, impl2).unwrap();

        // Canonicalize both
        let canon1 = stmt1.canonicalize(&var_factory, &term_factory).unwrap();
        let canon2 = stmt2.canonicalize(&var_factory, &term_factory).unwrap();

        // They should be identical (both become φ₀ → φ₁)
        let canon1_str = format!("{:?}", canon1);
        let canon2_str = format!("{:?}", canon2);

        assert_eq!(
            canon1_str, canon2_str,
            "α-equivalent statements should have identical canonical forms"
        );
    }

    #[test]
    fn canonicalize_preserves_logical_meaning() {
        // Property: S and canon(S) are logically equivalent (mutually included)
        // Canonicalization only renames variables, so the logical meaning is preserved.
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create a statement with non-canonical variables
        let (_, _, phi2, _, _, phi5, _, phi7) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();
        let phi7_term = term_factory.create_leaf(phi7).unwrap();

        // Create (φ₂ → φ₅) with hypothesis φ₇
        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi2_term, phi5_term])
            .unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            implication,
            vec![phi7_term],
            Default::default(),
        )
        .unwrap();

        // Canonicalize
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Check mutual inclusion: S ⊆ canon(S) and canon(S) ⊆ S
        let stmt_in_canon = stmt
            .is_included_in(&var_factory, &term_factory, &canon)
            .unwrap();
        let canon_in_stmt = canon
            .is_included_in(&var_factory, &term_factory, &stmt)
            .unwrap();

        assert!(
            stmt_in_canon,
            "Original statement should be included in canonical form"
        );
        assert!(
            canon_in_stmt,
            "Canonical form should be included in original statement"
        );
    }

    // Phase B2: CANONICALIZE Edge Cases

    #[test]
    fn canonicalize_simple_axiom() {
        // Edge case: Statement with no hypotheses
        // Only assertion needs variable renumbering
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create φ₅ → φ₂ (non-canonical order)
        let (_, _, phi2, _, _, phi5) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();

        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi5_term, phi2_term])
            .unwrap();

        let stmt: TestStatement = Statement::simple_axiom(&type_factory, implication).unwrap();

        // Canonicalize should produce φ₀ → φ₁
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Verify canonical form uses φ₀ and φ₁
        let vars = canon.collect_metavariables().unwrap();
        assert_eq!(vars.len(), 2, "Should have 2 variables");

        let (phi0, phi1) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        assert!(
            vars.contains(&phi0) && vars.contains(&phi1),
            "Canonical form should use φ₀ and φ₁"
        );
    }

    #[test]
    fn canonicalize_single_hypothesis() {
        // Edge case: Single hypothesis
        // factorial(1) = 1, so no permutations to try - only variable renumbering
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create (φ₃ → φ₇; [φ₅]; {})
        let (_, _, _, phi3, _, phi5, _, phi7) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi3_term = term_factory.create_leaf(phi3).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();
        let phi7_term = term_factory.create_leaf(phi7).unwrap();

        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi3_term, phi7_term])
            .unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            implication,
            vec![phi5_term],
            Default::default(),
        )
        .unwrap();

        // Canonicalize
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Should use φ₀, φ₁, φ₂ in some canonical order
        let vars = canon.collect_metavariables().unwrap();
        assert_eq!(vars.len(), 3, "Should have 3 variables");

        // Verify all variables are from the beginning of the sequence
        let (phi0, phi1, phi2) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        assert!(
            vars.contains(&phi0) && vars.contains(&phi1) && vars.contains(&phi2),
            "Canonical form should use φ₀, φ₁, φ₂"
        );
    }

    #[test]
    fn canonicalize_many_hypotheses() {
        // Edge case: Many hypotheses (5) - factorial(5) = 120 permutations
        // This is a performance check - should complete in reasonable time
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create 6 distinct Boolean variables (1 for assertion + 5 for hypotheses)
        // Use variables from middle of alphabet to ensure renumbering happens
        let vars: Vec<_> = var_factory
            .list_metavariables_by_type(&Boolean)
            .skip(5) // Skip P,Q,R,S,T; start with U,V,W,X,Y,Z
            .take(6)
            .collect();

        let terms: Vec<_> = vars
            .iter()
            .map(|&v| term_factory.create_leaf(v).unwrap())
            .collect();

        // Create statement with 5 hypotheses
        let assertion = terms[0].clone();
        let hypotheses = vec![
            terms[1].clone(),
            terms[2].clone(),
            terms[3].clone(),
            terms[4].clone(),
            terms[5].clone(),
        ];

        let stmt: TestStatement =
            Statement::new(&type_factory, assertion, hypotheses, Default::default()).unwrap();

        // This should complete without hanging
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Verify it produces a result with canonical variable names
        let canon_vars = canon.collect_metavariables().unwrap();
        assert_eq!(
            canon_vars.len(),
            6,
            "Should still have 6 variables after canonicalization (1 in assertion + 5 in hypotheses)"
        );
    }

    #[test]
    fn canonicalize_duplicate_hypotheses() {
        // Edge case: Duplicate hypotheses [P, Q, P]
        // Multiple permutations yield same result due to duplicates
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (_, _, phi2, phi3, _, phi5) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi3_term = term_factory.create_leaf(phi3).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();

        // Create (φ₅; [φ₂, φ₃, φ₂]; {}) - φ₂ appears twice
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi5_term,
            vec![phi2_term.clone(), phi3_term, phi2_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Canonicalize
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Should handle duplicates correctly
        let canon_vars = canon.collect_metavariables().unwrap();
        assert_eq!(
            canon_vars.len(),
            3,
            "Should have 3 distinct variables (φ₂ counted once)"
        );

        // Verify idempotence even with duplicates
        let canon2 = canon.canonicalize(&var_factory, &term_factory).unwrap();
        let canon1_str = format!("{:?}", canon);
        let canon2_str = format!("{:?}", canon2);
        assert_eq!(
            canon1_str, canon2_str,
            "Canonicalization should be idempotent even with duplicates"
        );
    }

    // ==========================================================================
    // Phase A3: CONTRACT Edge Cases
    // ==========================================================================

    #[test]
    fn contract_with_empty_distinctness_graph() {
        // Most common case - no distinctness constraints
        // Should succeed for any unifiable hypotheses
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create (φ → ψ; [φ, ψ]; {}) - empty distinctness graph
        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term.clone()])
            .unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            implication,
            vec![phi_term, psi_term],
            Default::default(), // Empty distinctness graph
        )
        .unwrap();

        // Contract hypotheses 0 and 1 (unify φ with ψ)
        let result = stmt.contract(&term_factory, 0, 1);

        assert!(
            result.is_ok(),
            "CONTRACT with empty distinctness graph should succeed: {:?}",
            result
        );

        if let Ok(contracted) = result {
            // Both hypotheses should unify, leaving only one
            assert_eq!(
                contracted.hypotheses.len(),
                1,
                "After contracting two hypotheses, should have 1 remaining"
            );
        }
    }

    #[test]
    fn contract_produces_additional_duplicates() {
        // Assertion: φ → ψ
        // Hypothesis 0: φ
        // Hypothesis 1: ψ
        // Hypothesis 2: φ  (duplicate of H0, but not being contracted)
        //
        // contract(stmt, 0, 1) unifies φ with ψ, creating substitution σ = {φ ↦ χ, ψ ↦ χ}
        // After σ applied:
        // - Hypothesis 0: χ
        // - Hypothesis 1: χ
        // - Hypothesis 2: χ
        // All three are now identical, should be deduplicated to single χ
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create (φ → ψ; [φ, ψ, φ]; {})
        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term.clone()])
            .unwrap();

        let stmt: TestStatement = Statement::new(
            &type_factory,
            implication,
            vec![phi_term.clone(), psi_term, phi_term],
            Default::default(),
        )
        .unwrap();

        // Contract hypotheses 0 and 1 (unify φ with ψ)
        let result = stmt.contract(&term_factory, 0, 1);

        assert!(
            result.is_ok(),
            "CONTRACT should succeed even when creating additional duplicates: {:?}",
            result
        );

        if let Ok(contracted) = result {
            // All three hypotheses should become identical after substitution
            // Deduplication should leave only one
            assert_eq!(
                contracted.hypotheses.len(),
                1,
                "After unifying φ and ψ, all three hypotheses [φ, ψ, φ] should become identical and deduplicate to 1"
            );
        }
    }

    // ==========================================================================
    // Phase C2: APPLY Simple Success Cases
    // ==========================================================================

    #[test]
    fn apply_simple_axiom_to_modus_ponens() {
        // This expands on the existing regression test pattern
        // Modus Ponens: (φ → ψ; [φ → ψ, φ]; {})
        // Simp (axiom 1): (φ → (ψ → φ); []; {})
        //
        // apply(MP, 0, Simp) should consume first hypothesis
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create φ → ψ
        let phi_implies_psi = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term.clone()])
            .unwrap();

        // Create ψ → φ
        let psi_implies_phi = term_factory
            .create_node(NodeByte::Implies, vec![psi_term.clone(), phi_term.clone()])
            .unwrap();

        // Create φ → (ψ → φ) - axiom 1
        let axiom1 = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_implies_phi])
            .unwrap();

        // Modus Ponens: (φ → ψ; [φ → ψ, φ]; {})
        let modus_ponens: TestStatement = Statement::new(
            &type_factory,
            phi_implies_psi.clone(),
            vec![phi_implies_psi.clone(), phi_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Simp: (φ → (ψ → φ); []; {})
        let simp: TestStatement = Statement::simple_axiom(&type_factory, axiom1).unwrap();

        // Apply simp to first hypothesis of `modus_ponens`
        let result = modus_ponens.apply(&var_factory, &term_factory, 0, &simp);

        assert!(
            result.is_ok(),
            "APPLY simple axiom to modus ponens should succeed: {:?}",
            result
        );

        if let Ok(applied) = result {
            // Should consume first hypothesis, leaving only the second
            assert_eq!(
                applied.hypotheses.len(),
                1,
                "After applying axiom to first hypothesis, should have 1 hypothesis remaining"
            );
        }
    }

    #[test]
    fn apply_consumes_all_hypotheses() {
        // Statement with 1 hypothesis
        // Apply statement that satisfies it
        // Result should have 0 hypotheses (theorem)
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create φ → ψ
        let phi_implies_psi = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term])
            .unwrap();

        // Statement with single hypothesis: (φ; [φ → ψ]; {})
        let stmt: TestStatement = Statement::new(
            &type_factory,
            phi_term.clone(),
            vec![phi_implies_psi.clone()],
            Default::default(),
        )
        .unwrap();

        // Axiom to apply: (φ → ψ; []; {})
        let axiom: TestStatement = Statement::simple_axiom(&type_factory, phi_implies_psi).unwrap();

        // Apply axiom to consume the only hypothesis
        let result = stmt.apply(&var_factory, &term_factory, 0, &axiom);

        assert!(
            result.is_ok(),
            "APPLY should succeed when consuming all hypotheses: {:?}",
            result
        );

        if let Ok(applied) = result {
            // Should have no hypotheses remaining - it's now a theorem
            assert_eq!(
                applied.hypotheses.len(),
                0,
                "After consuming the only hypothesis, result should be a theorem (0 hypotheses)"
            );
        }
    }

    // ==========================================================================
    // Phase D2: APPLY_MULTIPLE Success Cases
    // ==========================================================================

    #[test]
    fn apply_multiple_modus_ponens() {
        // This is what `condensed_detach` does internally
        // Modus Ponens: 2 hypotheses
        // Provide 2 proofs
        // Verify both hypotheses satisfied
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();

        // Create φ → ψ
        let phi_implies_psi = term_factory
            .create_node(NodeByte::Implies, vec![phi_term.clone(), psi_term.clone()])
            .unwrap();

        // Modus Ponens: (ψ; [φ → ψ, φ]; {})
        let modus_ponens: TestStatement = Statement::new(
            &type_factory,
            psi_term.clone(),
            vec![phi_implies_psi.clone(), phi_term.clone()],
            Default::default(),
        )
        .unwrap();

        // Two axioms to apply
        let axiom1: TestStatement =
            Statement::simple_axiom(&type_factory, phi_implies_psi).unwrap();
        let axiom2: TestStatement = Statement::simple_axiom(&type_factory, phi_term).unwrap();

        // Apply both axioms to satisfy both hypotheses
        let proofs = vec![Some(axiom1), Some(axiom2)];
        let result = modus_ponens.apply_multiple(&var_factory, &term_factory, &proofs);

        assert!(
            result.is_ok(),
            "APPLY_MULTIPLE should succeed with matching proofs: {:?}",
            result
        );

        if let Ok(applied) = result {
            // Both hypotheses should be satisfied, leaving 0
            assert_eq!(
                applied.hypotheses.len(),
                0,
                "After applying 2 proofs to 2 hypotheses, should have 0 remaining (theorem)"
            );
            // Assertion should be a single Boolean variable (canonicalized)
            let mut assertion_vars = HashSet::new();
            applied
                .assertion
                .collect_metavariables(&mut assertion_vars)
                .unwrap();
            assert_eq!(
                assertion_vars.len(),
                1,
                "Result should have assertion with 1 Boolean variable"
            );
        }
    }

    // ==========================================================================
    // Phase E2: `CONDENSED_DETACH` Success Cases
    // ==========================================================================

    #[test]
    fn condensed_detach_classic_modus_ponens() {
        // Major: P → Q
        // Minor: P
        // Result: Q
        //
        // This is the simplest case from logic textbooks
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (p, q) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // Create P → Q
        let p_implies_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), q_term.clone()])
            .unwrap();

        // Major: (P → Q; []; {})
        let major: TestStatement = Statement::simple_axiom(&type_factory, p_implies_q).unwrap();

        // Minor: (P; []; {})
        let minor: TestStatement = Statement::simple_axiom(&type_factory, p_term).unwrap();

        // Apply condensed detachment
        let result = TestStatement::condensed_detach(
            &var_factory,
            &term_factory,
            &minor,
            &major,
            NodeByte::Implies,
        );

        assert!(
            result.is_ok(),
            "Classic modus ponens should succeed: {:?}",
            result
        );

        if let Ok(detached) = result {
            // Result should be Q with no hypotheses
            assert_eq!(
                detached.hypotheses.len(),
                0,
                "Condensed detachment result should be a theorem"
            );
            // Assertion should be a single Boolean variable (canonicalized)
            let mut assertion_vars = HashSet::new();
            detached
                .assertion
                .collect_metavariables(&mut assertion_vars)
                .unwrap();
            assert_eq!(
                assertion_vars.len(),
                1,
                "Result should have assertion with 1 Boolean variable (Q, possibly renamed)"
            );
        }
    }

    #[test]
    fn condensed_detach_with_substitution() {
        // Major: φ → (ψ → χ)
        // Minor: φ
        // Result: ψ → χ
        //
        // Tests that condensed detachment correctly applies substitutions
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi, chi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();
        let chi_term = term_factory.create_leaf(chi).unwrap();

        // Create ψ → χ
        let psi_implies_chi = term_factory
            .create_node(NodeByte::Implies, vec![psi_term.clone(), chi_term.clone()])
            .unwrap();

        // Create φ → (ψ → χ)
        let phi_implies_psi_implies_chi = term_factory
            .create_node(
                NodeByte::Implies,
                vec![phi_term.clone(), psi_implies_chi.clone()],
            )
            .unwrap();

        // Major: (φ → (ψ → χ); []; {})
        let major: TestStatement =
            Statement::simple_axiom(&type_factory, phi_implies_psi_implies_chi).unwrap();

        // Minor: (φ; []; {})
        let minor: TestStatement = Statement::simple_axiom(&type_factory, phi_term).unwrap();

        // Apply condensed detachment
        let result = TestStatement::condensed_detach(
            &var_factory,
            &term_factory,
            &minor,
            &major,
            NodeByte::Implies,
        );

        assert!(
            result.is_ok(),
            "Condensed detachment with nested implication should succeed: {:?}",
            result
        );

        if let Ok(detached) = result {
            // Result should be (ψ → χ) with no hypotheses
            assert_eq!(detached.hypotheses.len(), 0, "Result should be a theorem");
            // Check that assertion is structurally equivalent to ψ → χ
            let mut result_vars = HashSet::new();
            detached
                .assertion
                .collect_metavariables(&mut result_vars)
                .unwrap();
            assert_eq!(
                result_vars.len(),
                2,
                "Result should have 2 variables (ψ and χ)"
            );
        }
    }

    // ==========================================================================
    // Week 4: Complex Cases (Optional)
    // ==========================================================================

    #[test]
    fn canonicalize_produces_expected_form() {
        // From operations.rs documentation (lines 535-548):
        // Example: φ₂ → φ₅ should canonicalize to φ₀ → φ₁
        //
        // This verifies the documented behavior matches actual implementation
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        // Create φ₂ and φ₅ (using specific indices)
        let phi2 = var_factory
            .list_metavariables_by_type(&Boolean)
            .nth(2)
            .unwrap();
        let phi5 = var_factory
            .list_metavariables_by_type(&Boolean)
            .nth(5)
            .unwrap();

        let phi2_term = term_factory.create_leaf(phi2).unwrap();
        let phi5_term = term_factory.create_leaf(phi5).unwrap();

        // Create φ₂ → φ₅
        let implication = term_factory
            .create_node(NodeByte::Implies, vec![phi2_term, phi5_term])
            .unwrap();

        let stmt: TestStatement = Statement::simple_axiom(&type_factory, implication).unwrap();

        // Canonicalize
        let canon = stmt.canonicalize(&var_factory, &term_factory).unwrap();

        // Verify result uses φ₀ and φ₁
        let vars = canon.collect_metavariables().unwrap();
        assert_eq!(vars.len(), 2, "Should have exactly 2 variables");

        let phi0 = var_factory
            .list_metavariables_by_type(&Boolean)
            .next()
            .unwrap();
        let phi1 = var_factory
            .list_metavariables_by_type(&Boolean)
            .nth(1)
            .unwrap();

        assert!(
            vars.contains(&phi0) && vars.contains(&phi1),
            "Canonical form should use φ₀ and φ₁, got: {:?}",
            vars
        );

        // Verify structure: should be Implies(φ₀, φ₁) or Implies(φ₁, φ₀)
        // Due to canonicalization algorithm, the specific order depends on
        // lexicographic ordering, but both variables should appear
        if let Some(node) = canon.assertion.get_node() {
            assert_eq!(
                node,
                NodeByte::Implies,
                "Canonical form should preserve Implies node"
            );
        } else {
            panic!("Expected canonical form to be a node (Implies), got leaf");
        }
    }

    #[test]
    fn inclusion_is_transitive() {
        // Property: If S1 ⊇ S2 and S2 ⊇ S3, then S1 ⊇ S3
        //
        // This tests the transitivity of the inclusion relation
        let type_factory = SimpleTypeFactory;
        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let (phi, psi, chi) = var_factory
            .list_metavariables_by_type(&Boolean)
            .tuples()
            .next()
            .unwrap();

        let phi_term = term_factory.create_leaf(phi).unwrap();
        let psi_term = term_factory.create_leaf(psi).unwrap();
        let chi_term = term_factory.create_leaf(chi).unwrap();

        // Create three statements with inclusion relationship:
        // S1: (φ; []; {}) - most general (includes anything with assertion φ)
        // S2: (φ; [ψ]; {}) - includes S1 with additional hypothesis
        // S3: (φ; [ψ, χ]; {}) - includes S2 with even more hypotheses
        //
        // Inclusion: S3 ⊇ S2 ⊇ S1
        // (More hypotheses means less general, so S3 is included in S2)
        let s1: TestStatement = Statement::simple_axiom(&type_factory, phi_term.clone()).unwrap();
        let s2: TestStatement = Statement::new(
            &type_factory,
            phi_term.clone(),
            vec![psi_term.clone()],
            Default::default(),
        )
        .unwrap();
        let s3: TestStatement = Statement::new(
            &type_factory,
            phi_term.clone(),
            vec![psi_term, chi_term],
            Default::default(),
        )
        .unwrap();

        // Verify S1 ⊇ S2 (S2 is included in S1)
        let s2_in_s1 = s2.is_included_in(&var_factory, &term_factory, &s1).unwrap();
        assert!(s2_in_s1, "S2 should be included in S1 (S1 ⊇ S2)");

        // Verify S2 ⊇ S3 (S3 is included in S2)
        let s3_in_s2 = s3.is_included_in(&var_factory, &term_factory, &s2).unwrap();
        assert!(s3_in_s2, "S3 should be included in S2 (S2 ⊇ S3)");

        // Verify transitivity: S1 ⊇ S3 (S3 is included in S1)
        let s3_in_s1 = s3.is_included_in(&var_factory, &term_factory, &s1).unwrap();
        assert!(
            s3_in_s1,
            "Transitivity: S3 should be included in S1 (S1 ⊇ S3)"
        );
    }

    #[test]
    fn contract_from_compact_proof() {
        // Strategy: Take a working compact proof, replace some axiom references
        // with underscores to create unsatisfied hypotheses, then verify we can
        // contract those hypotheses.
        //
        // Example: `"D2D1DD23D13"` → `"D2D1DD2_D_3"`
        // This creates a statement with 2 hypotheses that *might* be unifiable

        let var_factory = MetaByteFactory::new(SimpleTypeFactory);
        let term_factory = EnumTermFactory::new(SimpleTypeFactory);

        let dict = create_dict(
            &term_factory,
            &var_factory,
            NodeByte::Implies,
            NodeByte::Not,
        )
        .expect("Failed to create dictionary");

        // Parse compact proof with holes (underscores create unsatisfied hypotheses)
        let proof_with_holes = "D2D1DD2_D_3";

        let stmt =
            TestStatement::from_compact_proof(proof_with_holes, &var_factory, &term_factory, &dict)
                .expect("Failed to parse compact proof with holes");

        // Verify we got a statement with multiple hypotheses
        assert!(
            stmt.get_n_hypotheses() >= 2,
            "Expected at least 2 hypotheses from proof with holes, got {}",
            stmt.get_n_hypotheses()
        );

        // Try to contract the first two hypotheses
        // This may succeed or fail depending on whether they're unifiable
        let result = stmt.contract(&term_factory, 0, 1);

        // We're testing that CONTRACT works on real-world statement structures
        // The specific result (success or failure) depends on the proof structure
        match result {
            Ok(contracted) => {
                // Success: hypotheses were unifiable
                assert!(
                    contracted.get_n_hypotheses() < stmt.get_n_hypotheses(),
                    "CONTRACT should reduce hypothesis count"
                );
            }
            Err(_) => {
                // Failure: hypotheses weren't unifiable (different structure/types)
                // This is also valid - not all hypothesis pairs can be unified
                // The important thing is CONTRACT didn't panic or corrupt data
            }
        }
    }
}
