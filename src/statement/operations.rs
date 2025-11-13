//! Statement operations for proof construction.
//!
//! This module provides the core operations for building proofs:
//! - `contract`: Unify two hypotheses within a statement
//! - `relabel_disjoint`: Rename variables to avoid conflicts
//! - `apply`: Unify a hypothesis with another statement's assertion
//! - `apply_multiple`: Satisfy multiple hypotheses simultaneously
//! - `condensed_detach`: Meredith's condensed detachment (modus ponens application)

use super::base::Statement;
use crate::{
    apply_substitution,
    logic::{modus_ponens, MP_MAJOR_PREMISE, MP_MINOR_PREMISE},
    unify, DistinctnessGraph, Metavariable, MetavariableFactory, MguError, Node, Substitution,
    Term, TermFactory, Type,
};
use std::{collections::HashSet, marker::PhantomData};

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
    pub fn contract<TF>(&self, factory: &TF, n: usize, m: usize) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
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
            .ok_or(MguError::ChildIndexOutOfRange(n, self.hypotheses.len()))?;

        let hyp_m = self
            .hypotheses
            .get(m)
            .ok_or(MguError::ChildIndexOutOfRange(m, self.hypotheses.len()))?;

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
    fn apply_var_substitution<TF>(
        &self,
        term_factory: &TF,
        mapping: &std::collections::HashMap<V, V>,
    ) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
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
    pub fn relabel_disjoint<VF, TF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        avoid: &HashSet<V>,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
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
    pub fn apply<VF, TF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        n: usize,
        other: &Self,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Validate index
        let hyp_n = self
            .hypotheses
            .get(n)
            .ok_or(MguError::ChildIndexOutOfRange(n, self.hypotheses.len()))?;

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
    pub fn apply_multiple<VF, TF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        proofs: &[Option<Self>],
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
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
    ///
    /// # fn example() -> Result<(), MguError> {
    /// let var_factory = MetaByteFactory();
    /// let term_factory = EnumTermFactory::new();
    ///
    /// // Create P and (P → Q)
    /// let p = var_factory.create("P", &SimpleType::Boolean)?;
    /// let q = var_factory.create("Q", &SimpleType::Boolean)?;
    /// let p_term = term_factory.create_leaf(p)?;
    /// let q_term = term_factory.create_leaf(q)?;
    ///
    /// let p_implies_q = term_factory.create_node(
    ///     NodeByte::Implies,
    ///     vec![p_term.clone(), q_term.clone()]
    /// )?;
    ///
    /// // Build statements: minor = (P; ∅; ∅) and major = ((P → Q); ∅; ∅)
    /// let minor = Statement::simple_axiom(p_term)?;
    /// let major = Statement::simple_axiom(p_implies_q)?;
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
    pub fn condensed_detach<VF, TF>(
        var_factory: &VF,
        term_factory: &TF,
        minor: &Self,
        major: &Self,
        implies_node: N,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Create fresh Boolean metavariables for modus ponens
        let phi_var = var_factory
            .list_metavariables_by_type(&Ty::try_boolean()?)
            .next()
            .ok_or_else(|| {
                MguError::AllocationError("Could not create fresh Boolean variable φ".to_string())
            })?;

        let psi_var = var_factory
            .list_metavariables_by_type(&Ty::try_boolean()?)
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
    /// use symbolic_mgu::{Statement, MetaByte, Metavariable, SimpleType, NodeByte, Node};
    /// use symbolic_mgu::{EnumTerm, EnumTermFactory, MetaByteFactory};
    ///
    /// let var_factory = MetaByteFactory();
    /// let term_factory = EnumTermFactory::<SimpleType, MetaByte, NodeByte>::new();
    ///
    /// // Create φ₂ → φ₅ (non-canonical variables)
    /// let phi2 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 2).unwrap();
    /// let phi5 = MetaByte::try_from_type_and_index(SimpleType::Boolean, 5).unwrap();
    /// let implies = NodeByte::Implies;
    ///
    /// let phi2_term: EnumTerm<SimpleType, MetaByte, NodeByte> = EnumTerm::Leaf(phi2);
    /// let phi5_term = EnumTerm::Leaf(phi5);
    /// let implication = EnumTerm::NodeOrLeaf(implies, vec![phi2_term, phi5_term]);
    ///
    /// let stmt = Statement::simple_axiom(implication).unwrap();
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
    pub fn canonicalize<VF, TF>(
        &self,
        _var_factory: &VF,
        term_factory: &TF,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
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
                type_iterators.insert(typ.clone(), Box::new(V::enumerate(typ)));
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
}
