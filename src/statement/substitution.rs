//! Substitution operations on Statements.
//!
//! This module provides methods for applying substitutions to statements
//! and transforming distinctness graphs.

use super::base::Statement;
use crate::{
    apply_substitution, DistinctnessGraph, Metavariable, MguError, Node, Substitution, Term,
    TermFactory, Type, TypeFactory,
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
    /// Merge two distinctness graphs by taking the union of their edges.
    ///
    /// # Errors
    ///
    /// Returns an error if edge creation fails.
    pub(super) fn merge_distinctness_graphs(
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
    pub(super) fn collect_vars_from_term_static(term: &T) -> Result<HashSet<V>, MguError> {
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
    fn transform_distinctness_graph<TF, TyF>(
        &self,
        factory: &TF,
        subst: &Substitution<V, T>,
    ) -> Result<DistinctnessGraph<V>, MguError>
    where
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
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
    pub fn substitute<TF, TyF>(
        &self,
        factory: &TF,
        subst: &Substitution<V, T>,
    ) -> Result<Self, MguError>
    where
        TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermNode = N, TermMetavariable = V>,
        TyF: TypeFactory<Type = Ty>,
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
}
