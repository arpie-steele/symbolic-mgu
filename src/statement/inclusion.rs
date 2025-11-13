//! Statement inclusion and identity checking.
//!
//! This module implements the inclusion relationship between statements:
//! Statement S₁ includes S₂ (written S₁ ⊇ S₂) if there exists a substitution σ such that:
//! - A₁σ = A₂ (S₁'s assertion becomes S₂'s assertion after substitution)
//! - Each hypothesis in H₁σ equals some hypothesis in H₂ (H₁σ ⊆ H₂ as sets)
//! - D₂ is a super-graph of D₁σ (S₂ has at least S₁'s distinctness constraints)
//!
//! Intuitively: S₁ ⊇ S₂ means S₁ is **more general** and S₂ is **more specific**.
//! The substitution specializes S₁ into S₂.
//!
//! Equivalently, S₂ ⊆ S₁ (S₂ is included in S₁) expresses the same relation.
//!
//! ## Example
//!
//! Axiom `(P → P)` with no hypotheses **includes** statement `((x=x → y=y) → (x=x → y=y))`
//! with hypothesis `{x ∈ ℕ}` and distinctness `{x≠y}`, via substitution `σ = {P ↦ (x=x → y=y)}`.
//!
//! ## Design Note: Why No `PartialOrd`?
//!
//! Although inclusion forms a natural partial order, we do NOT implement `PartialOrd` for
//! `Statement`. Rust's `PartialOrd` requires `PartialEq`, but the natural equivalence for
//! statements (mutual inclusion) means "equal up to variable renaming", which conflicts
//! with Rust's expectation that `==` means structural equality. These are different concepts.
//!
//! Application code can wrap `Statement` in a new-type to implement these traits if desired.

use crate::{
    apply_substitution, unify, DistinctnessGraph, Metavariable, MetavariableFactory, MguError,
    Node, Statement, Substitution, Term, TermFactory, Type,
};

impl<Ty, V, N, T> Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// Check if this statement is included in another statement.
    ///
    /// Returns `true` if `self ⊆ other` (equivalently: `other ⊇ self`).
    ///
    /// This means `other` is **more general** than `self`, and there exists a substitution σ such that:
    /// - `A_other·σ = A_self` (`other`'s assertion becomes `self`'s assertion)
    /// - `H_other·σ ⊆ H_self` (`other`'s hypotheses, after σ, are subset of `self`'s)
    /// - `D_self ⊇ D_other·σ` (`self` has at least `other`'s distinctness constraints)
    ///
    /// The substitution σ applies only to variables from `other`, specializing it into `self`.
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating metavariables during relabeling
    /// * `term_factory` - Factory for creating and manipulating terms
    /// * `other` - The potentially more general statement to check against
    ///
    /// # Returns
    ///
    /// Returns `Ok(true)` if `self ⊆ other`, `Ok(false)` otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if term operations fail during checking.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{Statement, EnumTermFactory, MetaByte, MetaByteFactory, MetavariableFactory, NodeByte, SimpleType, TermFactory};
    /// use itertools::Itertools;
    ///
    /// let term_factory = EnumTermFactory::new();
    /// let var_factory = MetaByteFactory();
    ///
    /// // Create two simple axioms
    /// let (p, q) = var_factory
    ///         .list_metavariables_by_type(&SimpleType::Boolean)
    ///         .tuples()
    ///         .next()
    ///         .unwrap();
    ///
    /// // Create (P → P) - specific structure
    /// let p_term = term_factory.create_leaf(p).unwrap();
    /// let p_implies_p = term_factory.create_node(
    ///     NodeByte::Implies,
    ///     vec![p_term.clone(), p_term]
    /// ).unwrap();
    /// let s1 = Statement::simple_axiom(p_implies_p).unwrap();
    ///
    /// // Create Q - general variable
    /// let q_term = term_factory.create_leaf(q).unwrap();
    /// let s2 = Statement::simple_axiom(q_term).unwrap();
    ///
    /// // The specific structure is included in the general variable
    /// // (substitution: Q ↦ (P → P) makes s2's assertion equal s1's)
    /// assert!(s1.is_included_in(&var_factory, &term_factory, &s2).unwrap());
    ///
    /// // But the general variable is NOT included in the specific structure
    /// assert!(!s2.is_included_in(&var_factory, &term_factory, &s1).unwrap());
    /// ```
    pub fn is_included_in<VF, TF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        other: &Self,
    ) -> Result<bool, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Check if self ⊆ other (equivalently: other ⊇ self)
        // We need to find a substitution σ such that:
        // - `A_other·σ = A_self`
        // - For each h in `H_other`, h·σ equals some h in `H_self`
        // - `D_self` is a super-graph of `D_other·σ`
        //
        // Strategy: Build up a substitution by unifying components
        // 1. Start by unifying assertions
        // 2. Extend the substitution by matching hypotheses
        //
        // IMPORTANT: Relabel `other`'s variables to avoid conflicts with `self`'s variables.
        // Without this, occurs check failures prevent valid inclusions like:
        //   (Implies (Implies P Q) (Implies P Q)) ⊆ (Implies P P)
        // because unification would require P ↦ (Implies P Q), which violates occurs check.

        let self_vars = self.collect_metavariables()?;
        let other_relabeled = other.relabel_disjoint(var_factory, term_factory, &self_vars)?;

        let mut subst = match unify(term_factory, &other_relabeled.assertion, &self.assertion) {
            Ok(s) => s,
            Err(_) => return Ok(false), // Assertions don't unify - not included
        };

        // The unifier gives us `A_other·σ = A_self·σ`
        // We need `A_other·σ = A_self`, which means `A_self` must be unchanged by σ
        let self_assertion_subst = apply_substitution(term_factory, &subst, &self.assertion)?;

        if self_assertion_subst != self.assertion {
            // `self`'s assertion would be modified by σ, so `A_other·σ = A_self·σ ≠ A_self`
            return Ok(false);
        }

        // Now we know `A_self·σ = A_self`, so `A_other·σ = A_self·σ = A_self` ✓

        // Try to extend the substitution to match all of `other`'s hypotheses with `self`'s hypotheses
        // For each hypothesis in `other` (`H_other`), try to unify it with some hypothesis in `self` (`H_self`)
        for other_hyp in &other_relabeled.hypotheses {
            let mut matched = false;

            // First check if this hypothesis already matches with current substitution
            let other_hyp_subst = apply_substitution(term_factory, &subst, other_hyp)?;
            for self_hyp in &self.hypotheses {
                if &other_hyp_subst == self_hyp {
                    matched = true;
                    break;
                }
            }

            // If not matched, try to unify with each self hypothesis to extend substitution
            if !matched {
                for self_hyp in &self.hypotheses {
                    if let Ok(new_bindings) = unify(term_factory, other_hyp, self_hyp) {
                        // Try to merge `new_bindings` into subst
                        let mut extended_subst = subst.clone();
                        let mut can_extend = true;

                        for (var, term) in new_bindings.iter() {
                            if let Some(existing_term) = extended_subst.get(var) {
                                // Variable already bound - check compatibility
                                if existing_term != term {
                                    can_extend = false;
                                    break;
                                }
                            } else {
                                // Add new binding
                                extended_subst.extend(var.clone(), term.clone())?;
                            }
                        }

                        if can_extend {
                            // Check that `self`'s assertion is still unchanged
                            let self_assertion_check =
                                apply_substitution(term_factory, &extended_subst, &self.assertion)?;

                            if self_assertion_check == self.assertion {
                                // This extension works!
                                subst = extended_subst;
                                matched = true;
                                break;
                            }
                        }
                    }
                }
            }

            if !matched {
                return Ok(false); // Couldn't match this hypothesis
            }
        }

        // All hypotheses matched! Now check distinctness graph
        let other_dist_transformed = match Self::transform_distinctness_graph_static(
            term_factory,
            &other_relabeled.distinctness_graph,
            &subst,
        ) {
            Ok(g) => g,
            Err(_) => return Ok(false), // Distinctness constraint violation - not included
        };

        // Check that `self`'s distinctness graph is a super-graph of `other`'s transformed graph
        for (v1, v2) in other_dist_transformed.edges_iter() {
            // Check if this edge exists in self's distinctness graph
            let edge_found = self
                .distinctness_graph
                .edges_iter()
                .any(|(sv1, sv2)| (sv1 == v1 && sv2 == v2) || (sv1 == v2 && sv2 == v1));

            if !edge_found {
                return Ok(false); // Missing edge - not a super-graph
            }
        }

        Ok(true)
    }

    /// Check if this statement is identical to another statement.
    ///
    /// Two statements are identical if they mutually include each other:
    /// S₁ ≡ S₂ iff (S₁ ⊆ S₂ and S₂ ⊆ S₁), equivalently (S₁ ⊇ S₂ and S₂ ⊇ S₁).
    ///
    /// This means they differ only by variable renaming (α-equivalence).
    ///
    /// # Arguments
    ///
    /// * `var_factory` - Factory for creating metavariables during relabeling
    /// * `term_factory` - Factory for creating and manipulating terms
    /// * `other` - The statement to check identity against
    ///
    /// # Returns
    ///
    /// Returns `Ok(true)` if the statements are identical, `Ok(false)` otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if inclusion checking fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{Statement, EnumTermFactory, MetaByteFactory, MetavariableFactory, MetaByte, NodeByte, SimpleType, DistinctnessGraph, TermFactory};
    /// use itertools::Itertools;
    ///
    /// let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
    /// let var_factory = MetaByteFactory();
    ///
    /// let (p, q, r, s) = var_factory
    ///         .list_metavariables_by_type(&SimpleType::Boolean)
    ///         .tuples()
    ///         .next()
    ///         .unwrap();
    ///
    /// // Create two statements with same structure, different variable names:
    /// // s1: Q from P
    /// let p_term = term_factory.create_leaf(p).unwrap();
    /// let q_term = term_factory.create_leaf(q).unwrap();
    /// let s1 = Statement::new(q_term, vec![p_term], DistinctnessGraph::default()).unwrap();
    ///
    /// // s2: S from R
    /// let r_term = term_factory.create_leaf(r).unwrap();
    /// let s_term = term_factory.create_leaf(s).unwrap();
    /// let s2 = Statement::new(s_term, vec![r_term], DistinctnessGraph::default()).unwrap();
    ///
    /// // They are identical (differ only by variable renaming)
    /// assert!(s1.is_identical(&var_factory, &term_factory, &s2).unwrap());
    ///
    /// // Every statement is identical to itself
    /// assert!(s1.is_identical(&var_factory, &term_factory, &s1).unwrap());
    /// ```
    pub fn is_identical<VF, TF>(
        &self,
        var_factory: &VF,
        term_factory: &TF,
        other: &Self,
    ) -> Result<bool, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Check mutual inclusion
        let self_in_other = self.is_included_in(var_factory, term_factory, other)?;
        if !self_in_other {
            return Ok(false);
        }

        let other_in_self = other.is_included_in(var_factory, term_factory, self)?;
        Ok(other_in_self)
    }

    /// Transform a distinctness graph under a substitution (static version).
    ///
    /// This is a static version that can be used with any distinctness graph.
    ///
    /// # Errors
    ///
    /// Returns an error if distinctness constraints are violated.
    fn transform_distinctness_graph_static<TF>(
        term_factory: &TF,
        graph: &DistinctnessGraph<V>,
        subst: &Substitution<V, T>,
    ) -> Result<DistinctnessGraph<V>, MguError>
    where
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        let mut new_graph = DistinctnessGraph::new();

        // For each edge in the original graph
        for (v1, v2) in graph.edges_iter() {
            // Get the substituted terms for v1 and v2
            let term1 = if let Some(t) = subst.get(&v1) {
                t.clone()
            } else {
                // No substitution, use the variable itself
                term_factory.create_leaf(v1.clone())?
            };

            let term2 = if let Some(t) = subst.get(&v2) {
                t.clone()
            } else {
                term_factory.create_leaf(v2.clone())?
            };

            // Collect metavariables from both terms
            let vars1 = Self::collect_vars_from_term_static(&term1)?;
            let vars2 = Self::collect_vars_from_term_static(&term2)?;

            // Add edges between all pairs of metavariables from the two substitutions
            for var1 in &vars1 {
                for var2 in &vars2 {
                    new_graph.add_edge(var1, var2)?;
                }
            }
        }

        Ok(new_graph)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, NodeByte, SimpleType};
    use itertools::Itertools;

    /// Type aliases for tests
    type TestStatement =
        Statement<SimpleType, MetaByte, NodeByte, EnumTerm<SimpleType, MetaByte, NodeByte>>;

    /// Helper to create standard factories for tests
    fn setup() -> (
        EnumTermFactory<SimpleType, MetaByte, NodeByte>,
        MetaByteFactory,
    ) {
        (EnumTermFactory::new(), MetaByteFactory())
    }

    #[test]
    fn axiom_included_in_itself() {
        // Any statement should be included in itself
        let (term_factory, var_factory) = setup();

        let p = var_factory
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let stmt = TestStatement::simple_axiom(p_term).unwrap();

        assert!(stmt
            .is_included_in(&var_factory, &term_factory, &stmt)
            .unwrap());
    }

    #[test]
    fn axiom_identical_to_itself() {
        // Any statement should be identical to itself
        let (term_factory, var_factory) = setup();

        let p = var_factory
            .list_metavariables_by_type(&SimpleType::Boolean)
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let stmt = TestStatement::simple_axiom(p_term).unwrap();

        assert!(stmt
            .is_identical(&var_factory, &term_factory, &stmt)
            .unwrap());
    }

    #[test]
    fn more_specific_included_in_general() {
        // s1: Implies(P, P) (specific structure)
        // s2: Q (just a variable - general)
        // s1 ⊆ s2 (equivalently: s2 ⊇ s1) because σ = {Q ↦ Implies(P, P)} makes `A_s2·σ = A_s1`
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create Implies(P, P) - specific structure
        let p_term = term_factory.create_leaf(p).unwrap();
        let implies_p_p = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), p_term])
            .unwrap();
        let s1 = TestStatement::simple_axiom(implies_p_p).unwrap();

        // Create Q - just a variable (general)
        let q_term = term_factory.create_leaf(q).unwrap();
        let s2 = TestStatement::simple_axiom(q_term).unwrap();

        // s1 should be included in s2 (s2 is more general)
        assert!(s1.is_included_in(&var_factory, &term_factory, &s2).unwrap());

        // But s2 should NOT be included in s1
        assert!(!s2.is_included_in(&var_factory, &term_factory, &s1).unwrap());
    }

    #[test]
    fn different_variables_same_structure_are_identical() {
        // Statements with same structure but different variable names are identical
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q, r, s) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        // Create two statements with same structure, different variable names:
        // s1: Q from P
        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let s1 = TestStatement::new(q_term, vec![p_term], DistinctnessGraph::default()).unwrap();

        // s2: S from R
        let r_term = term_factory.create_leaf(r).unwrap();
        let s_term = term_factory.create_leaf(s).unwrap();
        let s2 = TestStatement::new(s_term, vec![r_term], DistinctnessGraph::default()).unwrap();

        // They should be identical (differ only by variable renaming)
        assert!(s1.is_identical(&var_factory, &term_factory, &s2).unwrap());
    }

    #[test]
    fn hypothesis_order_doesnt_matter() {
        // Statements with same hypotheses in different order should be identical
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q, r) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let r_term = term_factory.create_leaf(r).unwrap();

        // s1: R from [P, Q]
        let s1 = TestStatement::new(
            r_term.clone(),
            vec![p_term.clone(), q_term.clone()],
            DistinctnessGraph::default(),
        )
        .unwrap();

        // s2: R from [Q, P] (same hypotheses, different order)
        let s2 =
            TestStatement::new(r_term, vec![q_term, p_term], DistinctnessGraph::default()).unwrap();

        // They should be identical
        assert!(s1.is_identical(&var_factory, &term_factory, &s2).unwrap());
    }

    #[test]
    fn more_hypotheses_with_distinctness() {
        // With distinctness constraints, more hypotheses prevents collapsing via substitution
        // s1: R from [P, Q] with P≠Q (two distinct hypotheses)
        // s2: R from [P] (one hypothesis)
        // s1 ⊆ s2 because s2's hypothesis {P} is a subset of s1's hypotheses {P, Q}
        // s2 ⊄ s1 because collapsing to one hypothesis would violate P≠Q
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q, r) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();
        let r_term = term_factory.create_leaf(r).unwrap();

        // Create distinctness constraint P≠Q
        let mut dist_graph = DistinctnessGraph::default();
        dist_graph.add_edge(&p, &q).unwrap();

        // s1: R from [P, Q] with P≠Q
        let s1 = TestStatement::new(
            r_term.clone(),
            vec![p_term.clone(), q_term.clone()],
            dist_graph,
        )
        .unwrap();

        // s2: R from [P] (no distinctness)
        let s2 = TestStatement::new(r_term, vec![p_term], DistinctnessGraph::default()).unwrap();

        // s1 (more hypotheses with distinctness) IS included in s2
        assert!(s1.is_included_in(&var_factory, &term_factory, &s2).unwrap());

        // s2 is NOT included in s1 (would need Q↦P but P≠Q prevents this)
        assert!(!s2.is_included_in(&var_factory, &term_factory, &s1).unwrap());
    }

    #[test]
    fn unrelated_structures_not_included() {
        // Statements with incompatible structures are not included
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // s1: Implies(P, Q)
        let implies_p_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), q_term.clone()])
            .unwrap();
        let s1 = TestStatement::simple_axiom(implies_p_q).unwrap();

        // s2: Not(P) (different structure)
        let not_p = term_factory
            .create_node(NodeByte::Not, vec![p_term])
            .unwrap();
        let s2 = TestStatement::simple_axiom(not_p).unwrap();

        // They should not be included in each other
        assert!(!s1.is_included_in(&var_factory, &term_factory, &s2).unwrap());
        assert!(!s2.is_included_in(&var_factory, &term_factory, &s1).unwrap());
    }

    #[test]
    fn relabeling_prevents_occurs_check_failure() {
        // This test verifies that relabeling prevents occurs-check failures
        // when checking inclusion
        let (term_factory, var_factory) = setup();

        let vars = MetaByteFactory();
        let (p, q) = vars
            .list_metavariables_by_type(&SimpleType::Boolean)
            .tuples()
            .next()
            .unwrap();

        let p_term = term_factory.create_leaf(p).unwrap();
        let q_term = term_factory.create_leaf(q).unwrap();

        // s1: Implies(Implies(P, Q), Implies(P, Q))
        let implies_p_q = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), q_term.clone()])
            .unwrap();
        let implies_twice = term_factory
            .create_node(NodeByte::Implies, vec![implies_p_q.clone(), implies_p_q])
            .unwrap();
        let s1 = TestStatement::simple_axiom(implies_twice).unwrap();

        // s2: Implies(P, P) - more general
        let implies_p_p = term_factory
            .create_node(NodeByte::Implies, vec![p_term.clone(), p_term])
            .unwrap();
        let s2 = TestStatement::simple_axiom(implies_p_p).unwrap();

        // s1 should be included in s2
        // Without relabeling, this would fail with occurs-check because
        // we'd need P ↦ Implies(P, Q), but relabeling fixes this
        assert!(s1.is_included_in(&var_factory, &term_factory, &s2).unwrap());
    }
}
