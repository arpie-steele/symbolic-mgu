//! Introduce the [`Term`] trait which describes the tree used to
//! form Sentences.

use crate::{Metavariable, MguError, Node, Type};
use std::collections::HashSet;
use std::fmt::{Debug, Display};

/// A tree of (effectively) Nodes (some which may be leaves) and
/// Metavariables (always leaves).
pub trait Term: Sized + Clone + Debug + Display + PartialEq + Eq {
    /// Concrete implementation of the Type trait.
    type Type: Type;
    /// Concrete implementation of the Metavariable trait.
    type Metavariable: Metavariable;
    /// Concrete implementation of the Node trait.
    type Node: Node;

    /// TODO.
    ///
    /// # Errors
    /// - TODO.
    fn is_valid_sentence(&self) -> Result<bool, MguError>;

    /// TODO.
    fn is_valid_sentence_unchecked(&self) -> bool {
        self.is_valid_sentence().unwrap_or(false)
    }

    /// TODO.
    ///
    /// # Errors
    /// - TODO.
    fn get_type(&self) -> Result<Self::Type, MguError>;

    /// TODO.
    ///
    /// # Errors
    /// - TODO.
    fn collect_metavariables(
        &self,
        _vars: &mut HashSet<Self::Metavariable>,
    ) -> Result<(), MguError> {
        todo!();
    }
}
