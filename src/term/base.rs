//! Introduce the [`Term`] trait which describes the tree used to
//! form Sentences.

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
    /// [`Node`]: `crate::Node`
    fn is_metavariable(&self) -> bool;

    /// Return the leaf if this is a bare [`Metavariable`].
    fn get_metavariable(&self) -> Option<V>;

    /// Return the root [`Node`] if this is a sub-tree (which might have zero children).
    ///
    /// [`Node`]: `crate::Node`
    fn get_node(&self) -> Option<N>;

    /// Return the arity of the root of the tree.
    ///
    /// This is zero if the root is a [`Metavariable`] (or a [`Node`] with 0 slots).
    ///
    /// [`Node`]: `crate::Node`
    fn get_n_children(&self) -> usize;

    /// Get the indexed sub-tree.
    fn get_child(&self, index: usize) -> Option<&Self>;

    /// Get an iterator over all the sub-trees.
    fn get_children(&self) -> impl Iterator<Item = &Self>;

    /// Alternate to an iterator.
    fn get_children_as_slice(&self) -> &[Self];

    /// TODO.
    ///
    /// # Errors
    /// - TODO.
    fn is_valid_sentence(&self) -> Result<bool, MguError>;

    /// TODO.
    fn is_valid_sentence_unchecked(&self) -> bool {
        self.is_valid_sentence().unwrap_or(false)
    }

    /// Return the [`Type`] of this tree/sub-tree.
    ///
    /// # Errors
    /// - TODO.
    fn get_type(&self) -> Result<T, MguError>;

    /// TODO.
    ///
    /// # Errors
    /// - TODO.
    fn collect_metavariables(&self, _vars: &mut HashSet<V>) -> Result<(), MguError> {
        todo!();
    }

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
    /// use symbolic_mgu::{Term, EnumTerm, MetaByte, MetaByteFactory, MetavariableFactory, NodeByte, SimpleType, get_formatter};
    ///
    /// let vars = MetaByteFactory();
    /// let var = vars
    ///     .list_metavariables_by_type(&SimpleType::Boolean)
    ///     .next()
    ///     .unwrap();
    /// let term: EnumTerm<SimpleType, MetaByte, NodeByte> = EnumTerm::Leaf(var);
    /// let formatter = get_formatter("utf8");
    /// let output = term.format_with(&*formatter);
    /// assert_eq!(output, "P");
    /// ```
    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        let _ = formatter; // Suppress unused warning
        format!("{}", self) // Default: use Display
    }
}
