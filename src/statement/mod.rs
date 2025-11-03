//! Define the Statement type.

pub mod compact_proof;
pub mod inclusion;

use crate::{
    apply_substitution, unify, DistinctnessGraph, Metavariable, MetavariableFactory, MguError,
    Node, Substitution, Term, TermFactory, Type,
};
use std::{collections::HashSet, marker::PhantomData};

/// The primary object representing an axiom, inference rule, or
/// statement of a theorem.
#[derive(Debug, Default, Clone)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(
        bound = "T: serde::Serialize + serde::de::DeserializeOwned, V: serde::Serialize + serde::de::DeserializeOwned"
    )
)]
pub struct Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// This entry is literally not used.
    ///
    /// It functions to remind Rust that this object is tied to a certain Type.
    _not_used: PhantomData<(Ty, N)>,

    /// The assertion is a sentence which holds true when the
    /// hypotheses are met.
    pub(crate) assertion: T,

    /// The optional hypotheses control when the assertion is known
    /// to be true.
    pub(crate) hypotheses: Vec<T>,

    /// The distinctness graph controls what variable substitutions
    /// are illegal, typically because they threaten self-reference
    /// in impermissible ways.
    pub(crate) distinctness_graph: DistinctnessGraph<V>,
}

impl<Ty, V, N, T> Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// Create a new Statement from components.
    ///
    /// # Errors
    ///
    /// Returns an error if the assertion or any hypothesis is not
    /// a valid sentence (where the type is Boolean).
    pub fn new(
        assertion: T,
        hypotheses: Vec<T>,
        distinctness_graph: DistinctnessGraph<V>,
    ) -> Result<Self, MguError> {
        // Validate that assertion is a sentence (Boolean type)
        if !assertion.is_valid_sentence()? {
            return Err(MguError::from_found_and_expected_types(
                true,
                &(assertion.get_type()?),
                &(Ty::try_boolean()?),
            ));
        }

        // Validate that all hypotheses are sentences
        for (i, hyp) in hypotheses.iter().enumerate() {
            if !hyp.is_valid_sentence()? {
                return Err(MguError::UnificationFailure(format!(
                    "Hypothesis {i} is not a valid sentence (type {:?})",
                    hyp.get_type()
                )));
            }
        }

        Ok(Self {
            _not_used: PhantomData,
            assertion,
            hypotheses,
            distinctness_graph,
        })
    }

    /// Create a simple axiom (Statement with no hypotheses and
    /// empty distinctness graph).
    ///
    /// A simple axiom is a statement with:
    /// - An assertion (the axiom itself)
    /// - No hypotheses (empty list)
    /// - No distinctness constraints (empty graph)
    ///
    /// # Errors
    ///
    /// Returns an error if the assertion is not a valid sentence.
    pub fn simple_axiom(assertion: T) -> Result<Self, MguError>
    where
        V: Default,
    {
        Self::new(assertion, Vec::new(), DistinctnessGraph::default())
    }

    /// Access the Assertion Sentence.
    pub fn get_assertion(&self) -> &T {
        &self.assertion
    }

    /// Access the Hypotheses Sentences.
    pub fn get_hypotheses(&self) -> &Vec<T> {
        &self.hypotheses
    }

    /// Access the Hypotheses Sentences.
    pub fn get_n_hypotheses(&self) -> usize {
        self.hypotheses.len()
    }

    /// Access the Hypotheses Sentences.
    pub fn get_hypothesis(&self, index: usize) -> Option<&T> {
        self.hypotheses.get(index)
    }

    /// Access the `DistinctnessGraph`.
    pub fn get_distinctness_graph(&self) -> &DistinctnessGraph<V> {
        &self.distinctness_graph
    }

    /// Collect all metavariables used in this statement.
    ///
    /// # Errors
    /// - TODO.
    pub fn collect_metavariables(&self) -> Result<HashSet<V>, MguError> {
        let mut vars = HashSet::new();

        // Collect from assertion
        self.assertion.collect_metavariables(&mut vars)?;

        // Collect from all hypotheses
        for hyp in &self.hypotheses {
            hyp.collect_metavariables(&mut vars)?;
        }

        Ok(vars)
    }

    /// Merge two distinctness graphs by taking the union of their edges.
    ///
    /// # Errors
    ///
    /// Returns an error if edge creation fails.
    fn merge_distinctness_graphs(
        g1: &DistinctnessGraph<V>,
        g2: &DistinctnessGraph<V>,
    ) -> Result<DistinctnessGraph<V>, MguError> {
        let mut merged = DistinctnessGraph::new();

        // Add all edges from first graph
        for (v1, v2) in g1.edges_iter() {
            merged.add_edge(&v1, &v2)?;
        }

        // Add all edges from second graph
        for (v1, v2) in g2.edges_iter() {
            merged.add_edge(&v1, &v2)?;
        }

        Ok(merged)
    }

    /// Static helper to collect metavariables from a term.
    fn collect_vars_from_term_static(term: &T) -> Result<HashSet<V>, MguError> {
        let mut vars = HashSet::new();
        term.collect_metavariables(&mut vars)?;
        Ok(vars)
    }

    /// Transform the distinctness graph under a substitution.
    ///
    /// For each edge (`v1`, `v2`) in the original graph:
    /// - If `v1` and `v2` are both substituted with terms containing metavariables,
    ///   add edges between all metavariables in the `v1` substitution and all in the `v2` substitution
    /// - Validate that substituted terms for `v1` and `v2` don't share metavariables
    ///
    /// # Errors
    ///
    /// Returns an error if distinctness constraints are violated.
    fn transform_distinctness_graph<TF>(
        &self,
        factory: &TF,
        subst: &Substitution<V, T>,
    ) -> Result<DistinctnessGraph<V>, MguError>
    where
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        let mut new_graph = DistinctnessGraph::new();

        // For each edge in the original graph
        for (v1, v2) in self.distinctness_graph.edges_iter() {
            // Get the substituted terms for v1 and v2
            let term1 = if let Some(t) = subst.get(&v1) {
                t.clone()
            } else {
                // No substitution, use the variable itself as a term
                factory.create_leaf(v1.clone())?
            };

            let term2 = if let Some(t) = subst.get(&v2) {
                t.clone()
            } else {
                factory.create_leaf(v2.clone())?
            };

            // Collect metavariables from both terms
            let vars1 = Self::collect_vars_from_term_static(&term1)?;
            let vars2 = Self::collect_vars_from_term_static(&term2)?;

            // Check for overlap - this would be a distinctness violation
            let overlap: HashSet<_> = vars1.intersection(&vars2).cloned().collect();
            if !overlap.is_empty() {
                return Err(MguError::DistinctnessViolation(format!(
                    "Variables {} and {} are required to be distinct, but share metavariables after substitution",
                    v1, v2
                )));
            }

            // Add edges between all pairs of metavariables from the two substitutions
            for var1 in &vars1 {
                for var2 in &vars2 {
                    new_graph.add_edge(var1, var2)?;
                }
            }
        }

        Ok(new_graph)
    }

    /// Apply a substitution to this statement with distinctness validation.
    ///
    /// This validates that the substitution doesn't violate any distinctness constraints.
    ///
    /// # Arguments
    ///
    /// * `factory` - Term factory for creating leaf terms
    /// * `subst` - The substitution to apply (maps metavariables to terms)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Term construction fails
    /// - Distinctness constraints are violated
    pub fn substitute<TF>(&self, factory: &TF, subst: &Substitution<V, T>) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Apply substitution to assertion and hypotheses
        let new_assertion = apply_substitution(factory, subst, &self.assertion)?;

        let mut new_hypotheses = Vec::new();
        for hyp in &self.hypotheses {
            new_hypotheses.push(apply_substitution(factory, subst, hyp)?);
        }

        // Transform and validate distinctness graph
        let new_graph = self.transform_distinctness_graph(factory, subst)?;

        Ok(Self {
            _not_used: PhantomData,
            assertion: new_assertion,
            hypotheses: new_hypotheses,
            distinctness_graph: new_graph,
        })
    }

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
}
