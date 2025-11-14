//! Define an unordered pair of elements.

use crate::MguError;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt;
use std::ops::Index;

/// An *unordered* pair of two distinct elements, stored internally in a canonical order.
///
/// # Design philosophy
///
/// In an **undirected, simple graph**, each edge connects two distinct nodes without orientation
/// (i.e. `{a, b}` is the same edge as `{b, a}`) and without self-loops (`a != b`).
/// To enforce these constraints at the type level:
///
/// - Internally, a `Pair` stores its elements in ascending order (`.0 < .1`) using the natural
///   ordering of the type `U`. This guarantees a **unique representation** of each edge, so
///   `{a, b}` and `{b, a}` always normalize to the same `Pair`.
/// - Construction is only possible through [`Pair::new`] and [`Pair::make_pair`], which check both distinctness and
///   comparability, returning an error otherwise.
/// - By keeping the representation canonical, sets or maps of `Pair<U>` can be used directly
///   to model the edge set of an undirected, simple graph without risk of duplicates or
///   reversed edges.
///
/// # Examples
///
/// ```
/// # use symbolic_mgu::Pair;
/// let edge = Pair::new(2, 5).unwrap();
/// assert_eq!(edge[0], 2);
/// assert_eq!(edge[1], 5);
///
/// // Symmetry: (5, 2) normalizes to the same pair
/// let edge2 = Pair::new(5, 2).unwrap();
/// assert_eq!(edge, edge2);
/// ```
///
/// This makes `Pair` a natural building block for higher-level graph data structures.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(bound = "U: serde::Serialize + serde::de::DeserializeOwned")
)]
pub struct Pair<U>(pub(crate) U, pub(crate) U);

impl<U: fmt::Debug + PartialOrd> Pair<U> {
    /// Create `Pair` and enforce ordering and distinctness.
    ///
    /// # Errors
    ///
    /// It is an error if a == b or they are not comparable.
    pub fn new(a: U, b: U) -> Result<Self, MguError> {
        if a < b {
            Ok(Self(a, b))
        } else if b < a {
            Ok(Self(b, a))
        } else {
            Err(MguError::from_illegal_pair(
                &*format!("{a:?}"),
                &*format!("{b:?}"),
            ))
        }
    }

    /// Check the essential constraint on Pairs.
    ///
    /// # Errors
    ///
    /// It is an error if `self.0` ≥ `self.1` or they are not comparable.
    pub fn check(&self) -> Result<(), MguError> {
        if self.0 < self.1 {
            Ok(())
        } else {
            Err(MguError::from_illegal_pair(
                &*format!("{0:?}", self.0),
                &*format!("{0:?}", self.1),
            ))
        }
    }
}

impl<U: Clone + fmt::Debug + PartialOrd> Pair<U> {
    /// Make a pair.
    ///
    /// # Errors
    ///
    /// It is an error if a == b or they are not comparable.
    pub fn make_pair(a: &U, b: &U) -> Result<Self, MguError> {
        Self::new(a.clone(), b.clone())
    }
}

// impl<U> !Default for Pair<U> {}

impl<U: PartialEq> PartialEq for Pair<U> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<U: Eq> Eq for Pair<U> {}

impl<U: PartialEq + std::hash::Hash> std::hash::Hash for Pair<U> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<U: PartialOrd> PartialOrd for Pair<U> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => self.1.partial_cmp(&other.1),
            ord => ord,
        }
    }
}

impl<U: Ord> Ord for Pair<U> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}

impl<U: Clone> IntoIterator for Pair<U> {
    type Item = U;

    type IntoIter = std::array::IntoIter<U, 2>;

    fn into_iter(self) -> std::array::IntoIter<U, 2> {
        IntoIterator::into_iter([self.0, self.1])
    }
}

impl<U: Clone + fmt::Debug + PartialOrd> TryFrom<[U; 2]> for Pair<U> {
    type Error = MguError;

    fn try_from(value: [U; 2]) -> Result<Self, Self::Error> {
        Self::new(value[0].clone(), value[1].clone())
    }
}

impl<U: Clone + fmt::Debug + PartialOrd> TryFrom<&[U; 2]> for Pair<U> {
    type Error = MguError;

    fn try_from(value: &[U; 2]) -> Result<Self, Self::Error> {
        Self::new(value[0].clone(), value[1].clone())
    }
}

impl<U: Clone + fmt::Debug + PartialOrd> TryFrom<(U, U)> for Pair<U> {
    type Error = MguError;

    fn try_from(value: (U, U)) -> Result<Self, Self::Error> {
        Self::new(value.0, value.1)
    }
}

impl<U: Clone + fmt::Debug + PartialOrd> TryFrom<&(U, U)> for Pair<U> {
    type Error = MguError;

    fn try_from(value: &(U, U)) -> Result<Self, Self::Error> {
        Self::new(value.0.clone(), value.1.clone())
    }
}

impl<U> Index<bool> for Pair<U> {
    type Output = U;

    fn index(&self, index: bool) -> &Self::Output {
        match index {
            false => &self.0,
            true => &self.1,
        }
    }
}

/// Implement indexing for a comma-separated list of integer types.
macro_rules! impl_index_for_pair {
    ($($t:ty),*) => {
        $(
            impl<U> Index<$t> for Pair<U> {
                type Output = U;
                fn index(&self, index: $t) -> &Self::Output {
                    match index as usize {
                        0 => &self.0,
                        1 => &self.1,
                        _ => {
                            panic!("Index: {:?} is neither 0 nor 1.", index)
                        }
                    }
                }
            }

        )*
    }
}

impl_index_for_pair!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

impl<U> From<Pair<U>> for (U, U) {
    fn from(value: Pair<U>) -> Self {
        (value.0, value.1)
    }
}

impl<U> From<Pair<U>> for [U; 2] {
    fn from(value: Pair<U>) -> Self {
        [value.0, value.1]
    }
}

impl<U> From<Pair<U>> for Vec<U> {
    fn from(value: Pair<U>) -> Self {
        vec![value.0, value.1]
    }
}
