//! Compact proof parsing for condensed detachment.
//!
//! This module implements parsing of compact proof strings, a stack-based format
//! used to represent proofs in propositional calculus and condensed detachment.
//!
//! ## Compact Proof Format
//!
//! A compact proof is a string of tokens processed right-to-left:
//! - Statement keys (e.g., "D", "1", "2", "3") push statements onto the stack
//! - Underscores ("_") push placeholders (None) for unsatisfied hypotheses
//! - When a statement is pushed, it pops N items (N = hypothesis count) from the stack
//!
//! ### Example: "DD211"
//!
//! Given dictionary: D=Modus Ponens, 1=Simp, 2=Frege, 3=Transp
//!
//! Processing right-to-left:
//! 1. Token "1": Push Simp axiom (0 hypotheses) → Stack: \[Simp\]
//! 2. Token "1": Push Simp axiom → Stack: [Simp, Simp]
//! 3. Token "2": Push Frege axiom → Stack: [Frege, Simp, Simp]
//! 4. Token "D": Pop 2 items for MP, apply → Stack: [Lemma, Simp]
//! 5. Token "D": Pop 2 items for MP, apply → Stack: [Theorem: φ → φ]
//!
//! ### Example: "D__"
//!
//! Processing right-to-left:
//! 1. Token "_": Push None → Stack: [None]
//! 2. Token "_": Push None → Stack: [None, None]
//! 3. Token "D": Pop 2 items for MP (2 hypotheses), apply with [None, None]
//!    → Stack: [MP with 2 unsatisfied hypotheses]

use crate::{
    Metavariable, MetavariableFactory, MguError, Node, Statement, Term, TermFactory, Type,
};
use std::collections::HashMap;

impl<Ty, V, N, T> Statement<Ty, V, N, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    /// Parse a compact proof string into a Statement.
    ///
    /// # Arguments
    ///
    /// * `proof` - Compact proof string (e.g., "DD211", "D__")
    /// * `var_factory` - Factory for creating metavariables during relabeling
    /// * `term_factory` - Factory for creating and manipulating terms
    /// * `statements` - Dictionary mapping proof symbols to Statement objects
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{Statement, EnumTermFactory, MetaByteFactory, NodeByte, SimpleType};
    /// use symbolic_mgu::logic::create_dict;
    ///
    /// // Create factories and dictionary
    /// let term_factory = EnumTermFactory::new();
    /// let metavar_factory = MetaByteFactory();
    /// let dict = create_dict(&term_factory, &metavar_factory, NodeByte::Implies, NodeByte::Not).unwrap();
    ///
    /// // Parse "D__" (Modus Ponens with unsatisfied hypotheses)
    /// let mp_unsatisfied = Statement::from_compact_proof("D__", &metavar_factory, &term_factory, &dict).unwrap();
    /// assert_eq!(mp_unsatisfied.get_n_hypotheses(), 2);
    ///
    /// // Parse "DD211" (Proof of φ → φ)
    /// let phi_implies_phi = Statement::from_compact_proof("DD211", &metavar_factory, &term_factory, &dict).unwrap();
    /// assert_eq!(phi_implies_phi.get_n_hypotheses(), 0);
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Invalid token in proof string
    /// - Statement key not found in dictionary
    /// - Stack underflow or overflow
    /// - Unification fails during application
    ///
    /// # Panics
    ///
    /// This function does not panic. All `unwrap()` calls are guarded by explicit
    /// length checks with SAFETY comments explaining why they cannot fail.
    pub fn from_compact_proof<VF, TF>(
        proof: &str,
        var_factory: &VF,
        term_factory: &TF,
        statements: &HashMap<String, Self>,
    ) -> Result<Self, MguError>
    where
        VF: MetavariableFactory<Metavariable = V, MetavariableType = Ty>,
        TF: TermFactory<T, Ty, V, N, Term = T, TermNode = N, TermMetavariable = V>,
    {
        // Parse proof string into tokens (each character becomes a token)
        let tokens: Vec<String> = proof
            .chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '_' {
                    Ok(c.to_string())
                } else {
                    Err(MguError::UnificationFailure(format!(
                        "Invalid character in compact proof: '{}'",
                        c
                    )))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Stack for building proof
        let mut stack: Vec<Option<Self>> = Vec::new();

        // Process tokens right-to-left
        for token in tokens.iter().rev() {
            if token == "_" {
                // Placeholder for unsatisfied hypothesis
                stack.push(None);
            } else {
                // Look up statement in dictionary
                let stmt = statements.get(token).ok_or_else(|| {
                    MguError::UnificationFailure(format!(
                        "Unknown statement key in compact proof: '{}'",
                        token
                    ))
                })?;

                let n_hypotheses = stmt.get_n_hypotheses();

                // Pop N items from stack for N hypotheses
                if stack.len() < n_hypotheses {
                    return Err(MguError::UnificationFailure(format!(
                        "Stack underflow: need {} items for '{}', but stack has only {}",
                        n_hypotheses,
                        token,
                        stack.len()
                    )));
                }

                // Pop hypotheses in reverse order (to maintain correct order)
                let mut proofs = Vec::new();
                for _ in 0..n_hypotheses {
                    // SAFETY: We checked stack.len() >= `n_hypotheses` above (line 129),
                    // so this pop() will always succeed.
                    proofs.push(stack.pop().unwrap());
                }
                proofs.reverse();

                // Apply statement with collected proofs
                let result = stmt.apply_multiple(var_factory, term_factory, &proofs)?;

                // Push result onto stack
                stack.push(Some(result));
            }
        }

        // Final validation: stack should contain exactly one statement
        if stack.is_empty() {
            return Err(MguError::UnificationFailure(
                "Empty compact proof string".to_string(),
            ));
        }

        if stack.len() > 1 {
            return Err(MguError::UnificationFailure(format!(
                "Incomplete proof: stack has {} items remaining",
                stack.len()
            )));
        }

        // SAFETY: We checked stack is not empty above (line 154),
        // so this pop() will always succeed.
        stack.pop().unwrap().ok_or_else(|| {
            MguError::UnificationFailure("Final result is a placeholder (None)".to_string())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        logic::create_dict, EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, NodeByte,
        SimpleType,
    };

    /// Type alias for test statement
    type TestStatement =
        Statement<SimpleType, MetaByte, NodeByte, EnumTerm<SimpleType, MetaByte, NodeByte>>;

    /// Helper to create standard dictionary for tests
    fn setup() -> (
        EnumTermFactory<SimpleType, MetaByte, NodeByte>,
        MetaByteFactory,
        HashMap<String, TestStatement>,
    ) {
        let term_factory = EnumTermFactory::new();
        let metavar_factory = MetaByteFactory();
        let dict = create_dict(
            &term_factory,
            &metavar_factory,
            NodeByte::Implies,
            NodeByte::Not,
        )
        .unwrap();
        (term_factory, metavar_factory, dict)
    }

    #[test]
    fn d_with_placeholders() {
        let (term_factory, metavar_factory, dict) = setup();

        // Parse "D__" (Modus Ponens with 2 unsatisfied hypotheses)
        let result =
            Statement::from_compact_proof("D__", &metavar_factory, &term_factory, &dict).unwrap();

        // Should have 2 hypotheses (both unsatisfied)
        assert_eq!(result.get_n_hypotheses(), 2);
    }

    #[test]
    fn dd211_phi_implies_phi() {
        let (term_factory, metavar_factory, dict) = setup();

        // Parse "DD211" (Proof of φ → φ)
        let result =
            Statement::from_compact_proof("DD211", &metavar_factory, &term_factory, &dict).unwrap();

        // Should have no hypotheses (complete proof)
        assert_eq!(result.get_n_hypotheses(), 0);

        // The assertion should be of form (φ → φ)
        // We can't easily check the exact structure without more introspection,
        // but we can verify it's a Boolean sentence
        assert!(result.get_assertion().is_valid_sentence().unwrap());
    }

    #[test]
    fn empty_proof_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // Empty proof string should fail
        let result = Statement::from_compact_proof("", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }

    #[test]
    fn invalid_token_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // Invalid character should fail
        let result = Statement::from_compact_proof("D@_", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }

    #[test]
    fn unknown_statement_key_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // Unknown key 'X' should fail
        let result = Statement::from_compact_proof("DX_", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }

    #[test]
    fn stack_underflow_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // "D" needs 2 items but we only have 1 placeholder
        let result = Statement::from_compact_proof("D_", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }

    #[test]
    fn incomplete_proof_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // "1" pushes an axiom, but then there's nothing to apply it to
        // This leaves 2 items on stack instead of 1
        let result = Statement::from_compact_proof("11", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }

    #[test]
    fn axioms_directly() {
        let (term_factory, metavar_factory, dict) = setup();

        // Single axioms should work (they have 0 hypotheses)
        let simp =
            Statement::from_compact_proof("1", &metavar_factory, &term_factory, &dict).unwrap();
        assert_eq!(simp.get_n_hypotheses(), 0);

        let frege =
            Statement::from_compact_proof("2", &metavar_factory, &term_factory, &dict).unwrap();
        assert_eq!(frege.get_n_hypotheses(), 0);

        let transp =
            Statement::from_compact_proof("3", &metavar_factory, &term_factory, &dict).unwrap();
        assert_eq!(transp.get_n_hypotheses(), 0);
    }

    #[test]
    fn final_placeholder_fails() {
        let (term_factory, metavar_factory, dict) = setup();

        // Just a placeholder should fail (final result can't be None)
        let result = Statement::from_compact_proof("_", &metavar_factory, &term_factory, &dict);
        assert!(result.is_err());
    }
}
