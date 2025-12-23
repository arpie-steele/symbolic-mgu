//! Introduce the [`Term`] trait which describes the tree used to
//! form Sentences.

use crate::formatter::OutputFormatter;
use crate::{Metavariable, MguError, Node, Type};
use std::collections::HashSet;
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Trait to create tree-like structure of [`Node`]s and [`Metavariable`]s while enforcing
/// the constraints of the [`Type`]s and the fixed arities of the children of the [`Node`]s.
///
/// # Formal Statement
///
/// A tree τ is either:
/// * A [`Metavariable`] xᵗ, or
/// * An application N(τ₁, ..., τₖ) where N is a [`Node`] of arity k,
///   and each τᵢ is a tree of TYPE matching the ith slot of N.
///
/// We define TYPE(τ) as:
/// * TYPE(xᵗ) = t
/// * TYPE(N(τ₁,...,τₖ)) = TYPE(N)
///
/// The `Ord` bound is required to support statement canonicalization,
/// which produces a unique minimal representation by ordering terms
/// lexicographically.
///
/// [`Node`]: `crate::Node`
pub trait Term<T, V, N>:
    Debug + Display + PartialEq + Eq + Hash + Clone + PartialOrd + Ord
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    /// Concrete implementation of the Type trait.
    type Type: Type;
    /// Concrete implementation of the Metavariable trait.
    type Metavariable: Metavariable;
    /// Concrete implementation of the Node trait.
    type Node: Node;

    /// Return `true` if this tree is a bare [`Metavariable`] (leaf)
    /// and `false` if it is a tree with a root of [`Node`]
    /// (which still might have zero children).
    ///
    /// # Invariant
    ///
    /// This method MUST be consistent with [`Term::get_metavariable`]:
    /// - `is_metavariable()` returns `true` iff `get_metavariable()` returns `Some(_)`
    /// - `is_metavariable()` returns `false` iff `get_metavariable()` returns `None`
    ///
    /// The default implementation enforces this by calling `get_metavariable()`.
    /// Implementations may override for performance if they can check without allocation.
    ///
    /// [`Node`]: `crate::Node`
    #[must_use]
    fn is_metavariable(&self) -> bool {
        self.get_metavariable().is_some()
    }

    /// Return the leaf if this is a bare [`Metavariable`].
    ///
    /// Returns `Some(metavariable)` if this term is a leaf metavariable,
    /// or `None` if this is a node application.
    ///
    /// # Invariant
    ///
    /// This method MUST be consistent with [`Term::is_metavariable`]:
    /// - Returns `Some(_)` iff `is_metavariable()` returns `true`
    /// - Returns `None` iff `is_metavariable()` returns `false`
    #[must_use]
    fn get_metavariable(&self) -> Option<V>;

    /// Return the root [`Node`] if this is a sub-tree (which might have zero children).
    ///
    /// [`Node`]: `crate::Node`
    #[must_use]
    fn get_node(&self) -> Option<N>;

    /// Return the arity of the root of the tree.
    ///
    /// This is zero if the root is a [`Metavariable`] (or a [`Node`] with 0 slots).
    ///
    /// [`Node`]: `crate::Node`
    #[must_use]
    fn get_n_children(&self) -> usize;

    /// Get the indexed sub-tree.
    #[must_use]
    fn get_child(&self, index: usize) -> Option<&Self>;

    /// Get an iterator over all the sub-trees.
    #[must_use]
    fn get_children(&self) -> impl Iterator<Item = &Self>;

    /// Alternate to an iterator.
    #[must_use]
    fn get_children_as_slice(&self) -> &[Self];

    /// Check if this term is structurally well-formed.
    ///
    /// A term is structurally valid if:
    /// - All metavariables are well-formed (have valid type and index)
    /// - All nodes have the correct number of children for their arity
    /// - All children have types compatible with the node's slot types
    ///
    /// Note: This does NOT check if the root has Boolean type. That check
    /// is performed separately by [`Statement::new`] to allow flexibility
    /// for users who want different type requirements.
    ///
    /// # Errors
    ///
    /// Returns an error if type checking fails or structural validation encounters
    /// malformed nodes/metavariables.
    ///
    /// [`Statement::new`]: `crate::Statement::new`
    fn is_valid_sentence(&self) -> Result<bool, MguError>;

    /// Check if this term is a valid sentence, returning `false` on any error.
    ///
    /// This is a convenience method that converts errors to `false`.
    /// Use [`Term::is_valid_sentence`] if you need to distinguish between
    /// validation failures and structural errors.
    #[must_use]
    fn is_valid_sentence_unchecked(&self) -> bool {
        self.is_valid_sentence().unwrap_or(false)
    }

    /// Return the [`Type`] of this tree/sub-tree.
    ///
    /// For a metavariable, returns its declared type.
    /// For a node application, returns the node's output type.
    ///
    /// # Errors
    ///
    /// Returns an error if the term structure is malformed or if
    /// type information cannot be determined.
    fn get_type(&self) -> Result<T, MguError>;

    /// Recursively collect all metavariables appearing in this term.
    ///
    /// This method traverses the term tree and inserts all metavariables
    /// into the provided `HashSet`. For a leaf metavariable, inserts just
    /// that variable. For a node application, recursively collects from
    /// all children.
    ///
    /// # Arguments
    ///
    /// * `vars` - `HashSet` to insert metavariables into
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The term structure is malformed
    /// - Metavariable information cannot be accessed
    /// - Database-backed implementations encounter I/O errors
    ///
    /// Note: The current `EnumTerm` implementation never returns an error,
    /// but the trait allows for fallible implementations to support
    /// database-backed or validated term structures.
    fn collect_metavariables(&self, vars: &mut HashSet<V>) -> Result<(), MguError>;

    /// Pre-flight syntax check to see if the supplied children are compatible with the supplied [`Node`].
    ///
    /// # Errors
    ///
    /// Will return Err if a syntax error is found, including
    /// * Wrong number of children
    /// * The type of a sub-tree cannot be assigned to the associated slot of the [`Node`]
    ///
    /// [`Node`]: `crate::Node`
    fn check_children(node: &N, children: &[Self]) -> Result<(), MguError> {
        let wanted_children = node.get_arity()?;
        let actual_children = children.len();
        if wanted_children < actual_children {
            return Err(MguError::from_found_and_expected_unsigned(
                actual_children,
                wanted_children,
            ));
        }
        if wanted_children > actual_children {
            return Err(MguError::from_found_and_expected_unsigned(
                actual_children,
                wanted_children,
            ));
        }
        for (i, term) in children.iter().enumerate() {
            let slot_type = node.get_slot_type(i)?;
            let term_type = term.get_type()?;
            if !term_type.is_subtype_of(&slot_type) {
                return Err(MguError::from_found_and_expected_types(
                    true, &term_type, &slot_type,
                ));
            }
        }
        Ok(())
    }

    /// Format this term with the given formatter.
    ///
    /// This method allows terms to customize their representation
    /// based on the formatter being used. Different formatters support
    /// different output formats (ASCII, UTF-8, LaTeX, HTML, etc.).
    ///
    /// # Default Implementation
    ///
    /// The default implementation delegates to the Display trait.
    /// Concrete implementations should override this to provide
    /// formatter-specific recursive rendering.
    ///
    /// # Arguments
    ///
    /// * `formatter` - The formatter to use for rendering
    ///
    /// # Examples
    ///
    /// ```rust
    /// use symbolic_mgu::{Term, EnumTerm, MetaByte, MetaByteFactory, MetavariableFactory, NodeByte, SimpleType, SimpleTypeFactory, get_formatter};
    /// use SimpleType::*;
    ///
    /// let vars = MetaByteFactory::new(SimpleTypeFactory);
    /// let var = vars
    ///     .list_metavariables_by_type(&Boolean)
    ///     .next()
    ///     .unwrap();
    /// let term: EnumTerm<SimpleType, MetaByte, NodeByte> = EnumTerm::Leaf(var);
    /// let formatter = get_formatter("utf8");
    /// let output = term.format_with(&*formatter);
    /// assert_eq!(output, "P");
    /// ```
    #[must_use]
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        let _ = formatter; // Suppress unused warning
        format!("{}", self) // Default: use Display
    }
}

#[cfg(test)]
mod tests {
    /// Verify that Term trait is NOT dyn-safe due to Clone, Eq, Hash, Ord.
    ///
    /// Term intentionally requires these traits for use in collections and
    /// canonicalization, making it incompatible with trait objects.
    /// This is the correct design - Term is used as a concrete type parameter,
    /// not as a trait object.
    #[test]
    fn term_is_not_dyn_safe() {
        // This test documents that Term is NOT dyn-safe by design.
        // The following line would NOT compile (commented out to prevent error):
        //
        // let _: &dyn Term = todo!();
        //
        // Error: Term is not dyn-safe because it requires Clone, Eq, Hash, PartialOrd, Ord
        // which use Self as a type parameter.
        //
        // This is intentional - Term is used as a concrete type in generics like
        // Statement<Ty, V, N, T>, not as a trait object.
    }
}
