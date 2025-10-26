//! Introduce the [`Term`] trait which describes the tree used to
//! form Sentences.

use crate::{Metavariable, Type};
use std::collections::HashSet;
use std::fmt::{Debug, Display};

/// A tree of (effectively) Nodes (some which may be leaves) and
/// Metavariables (always leaves).
pub trait Term: Sized + Clone + Debug + Display + PartialEq + Eq {
    /// TODO.
    fn is_valid_sentence(&self) -> bool;
    /// TODO.
    fn get_type(&self) -> Type;
    /// TODO.
    fn collect_metavariables<V: Metavariable>(&self, _vars: &mut HashSet<V>) {
        todo!();
    }
}
