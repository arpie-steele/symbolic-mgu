//! Introduce the [`Term`] trait which describes the tree used to form Sentences.

use std::fmt::{Debug, Display};

/// A tree of (effectively) Nodes (some which may be leafs) and Nodes (always leafs).
pub trait Term: Sized + Clone + Debug + Display + PartialEq + Eq {}
