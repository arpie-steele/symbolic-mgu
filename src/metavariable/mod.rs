//! Introduce the [`Metavariable`] trait which has ready-made short and wide implementations.

use std::fmt::{Debug, Display};
use std::hash::Hash;

/// Trait encapsulating behavior of the metavariable type.
///
/// TODO.
pub trait Metavariable: Sized + Display + Debug + Clone + Copy + Hash + PartialEq + Eq {}
