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
#[derive(Clone, Debug)]
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

impl<U: Copy> Copy for Pair<U> {}

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
///
/// # Panics
///
/// Panics if index is not 0 or 1, as `Pair` contains exactly two elements.
/// This follows the standard Rust convention for `Index` trait implementations.
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
                            panic!("Pair index out of bounds: {} (Pair has only 2 elements, valid indices are 0 and 1)", index)
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

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Construction Tests
    // =========================================================================

    #[test]
    fn new_creates_pair_in_order() {
        // When a < b, pair should be (a, b)
        let pair = Pair::new(1, 5).unwrap();
        assert_eq!(pair.0, 1);
        assert_eq!(pair.1, 5);
    }

    #[test]
    fn new_swaps_if_needed() {
        // When b < a, pair should swap to (b, a)
        let pair = Pair::new(5, 1).unwrap();
        assert_eq!(pair.0, 1);
        assert_eq!(pair.1, 5);
    }

    #[test]
    fn new_rejects_equal_elements() {
        // Pairs must be distinct
        let result = Pair::new(3, 3);
        assert!(result.is_err(), "Should reject pair with equal elements");
    }

    #[test]
    fn new_symmetric_pairs_are_equal() {
        // (a, b) and (b, a) should create identical pairs
        let pair1 = Pair::new(2, 7).unwrap();
        let pair2 = Pair::new(7, 2).unwrap();
        assert_eq!(pair1, pair2);
    }

    #[test]
    fn make_pair_clones_elements() {
        let a = String::from("alpha");
        let b = String::from("beta");

        let pair = Pair::make_pair(&a, &b).unwrap();

        // Should still be able to use original values
        assert_eq!(a, "alpha");
        assert_eq!(b, "beta");
        assert_eq!(pair.0, "alpha");
        assert_eq!(pair.1, "beta");
    }

    #[test]
    fn make_pair_rejects_equal_elements() {
        let x = 42;
        let result = Pair::make_pair(&x, &x);
        assert!(result.is_err(), "make_pair should reject equal elements");
    }

    // =========================================================================
    // Validation Tests
    // =========================================================================

    #[test]
    fn check_validates_proper_pair() {
        let pair = Pair::new(10, 20).unwrap();
        assert!(pair.check().is_ok(), "Valid pair should pass check()");
    }

    // =========================================================================
    // Trait Implementation Tests
    // =========================================================================

    #[test]
    fn partial_eq_compares_correctly() {
        let pair1 = Pair::new(1, 2).unwrap();
        let pair2 = Pair::new(1, 2).unwrap();
        let pair3 = Pair::new(1, 3).unwrap();
        let pair4 = Pair::new(2, 3).unwrap();

        assert_eq!(pair1, pair2);
        assert_ne!(pair1, pair3);
        assert_ne!(pair1, pair4);
    }

    #[test]
    fn hash_consistent_for_equal_pairs() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let pair1 = Pair::new(5, 10).unwrap();
        let pair2 = Pair::new(10, 5).unwrap(); // Should normalize to same pair

        let mut hasher1 = DefaultHasher::new();
        pair1.hash(&mut hasher1);
        let hash1 = hasher1.finish();

        let mut hasher2 = DefaultHasher::new();
        pair2.hash(&mut hasher2);
        let hash2 = hasher2.finish();

        assert_eq!(hash1, hash2, "Equal pairs should have equal hashes");
    }

    #[test]
    fn partial_ord_lexicographic_ordering() {
        let _pair_11 = Pair::new(1, 1).ok(); // Will fail, but let's use valid ones
        let pair_12 = Pair::new(1, 2).unwrap();
        let pair_13 = Pair::new(1, 3).unwrap();
        let _pair_22 = Pair::new(2, 2).ok(); // Will fail
        let pair_23 = Pair::new(2, 3).unwrap();

        // (1,2) < (1,3) because first elements equal, second is less
        assert!(pair_12 < pair_13);

        // (1,3) < (2,3) because first element is less
        assert!(pair_13 < pair_23);

        // (1,2) < (2,3)
        assert!(pair_12 < pair_23);
    }

    #[test]
    fn ord_consistent_with_partial_ord() {
        use std::cmp::Ordering;

        let pair1 = Pair::new(1, 5).unwrap();
        let pair2 = Pair::new(2, 3).unwrap();

        // Ord::`cmp` should match PartialOrd::`partial_cmp`
        assert_eq!(pair1.cmp(&pair2), Ordering::Less);
        assert_eq!(pair1.partial_cmp(&pair2), Some(Ordering::Less));
    }

    // =========================================================================
    // IntoIterator Tests
    // =========================================================================

    #[test]
    fn into_iter_yields_both_elements() {
        let pair = Pair::new(10, 20).unwrap();
        let vec: Vec<i32> = pair.into_iter().collect();

        assert_eq!(vec, vec![10, 20]);
    }

    // =========================================================================
    // TryFrom Tests
    // =========================================================================

    #[test]
    fn try_from_array_succeeds() {
        let arr = [3, 7];
        let pair = Pair::try_from(arr).unwrap();

        assert_eq!(pair.0, 3);
        assert_eq!(pair.1, 7);
    }

    #[test]
    fn try_from_array_ref_succeeds() {
        let arr = [3, 7];
        let pair = Pair::try_from(&arr).unwrap();

        assert_eq!(pair.0, 3);
        assert_eq!(pair.1, 7);
    }

    #[test]
    fn try_from_array_rejects_equal() {
        let arr = [5, 5];
        let result = Pair::try_from(arr);

        assert!(result.is_err(), "Should reject array with equal elements");
    }

    #[test]
    fn try_from_tuple_succeeds() {
        let tuple = (8, 2);
        let pair = Pair::try_from(tuple).unwrap();

        // Should normalize to (2, 8)
        assert_eq!(pair.0, 2);
        assert_eq!(pair.1, 8);
    }

    #[test]
    fn try_from_tuple_ref_succeeds() {
        let tuple = (8, 2);
        let pair = Pair::try_from(&tuple).unwrap();

        assert_eq!(pair.0, 2);
        assert_eq!(pair.1, 8);
    }

    #[test]
    fn try_from_tuple_rejects_equal() {
        let tuple = (4, 4);
        let result = Pair::try_from(tuple);

        assert!(result.is_err(), "Should reject tuple with equal elements");
    }

    // =========================================================================
    // Index Tests
    // =========================================================================

    #[test]
    fn index_bool_false_returns_first() {
        let pair = Pair::new(100, 200).unwrap();
        assert_eq!(pair[false], 100);
    }

    #[test]
    fn index_bool_true_returns_second() {
        let pair = Pair::new(100, 200).unwrap();
        assert_eq!(pair[true], 200);
    }

    #[test]
    fn index_usize_0_returns_first() {
        let pair = Pair::new(42, 99).unwrap();
        assert_eq!(pair[0], 42);
    }

    #[test]
    fn index_usize_1_returns_second() {
        let pair = Pair::new(42, 99).unwrap();
        assert_eq!(pair[1], 99);
    }

    #[test]
    #[should_panic(expected = "Pair index out of bounds")]
    fn index_usize_out_of_bounds_panics() {
        let pair = Pair::new(1, 2).unwrap();
        let _ = pair[2]; // Should panic
    }

    #[test]
    fn index_i32_works() {
        let pair = Pair::new(10, 20).unwrap();
        assert_eq!(pair[0i32], 10);
        assert_eq!(pair[1i32], 20);
    }

    #[test]
    #[should_panic(expected = "Pair index out of bounds")]
    fn index_i32_out_of_bounds_panics() {
        let pair = Pair::new(1, 2).unwrap();
        let _ = pair[5i32]; // Should panic
    }

    // =========================================================================
    // From Conversions Tests
    // =========================================================================

    #[test]
    fn from_pair_to_tuple() {
        let pair = Pair::new(3, 7).unwrap();
        let tuple: (i32, i32) = pair.into();

        assert_eq!(tuple, (3, 7));
    }

    #[test]
    fn from_pair_to_array() {
        let pair = Pair::new(5, 9).unwrap();
        let arr: [i32; 2] = pair.into();

        assert_eq!(arr, [5, 9]);
    }

    #[test]
    fn from_pair_to_vec() {
        let pair = Pair::new(11, 22).unwrap();
        let vec: Vec<i32> = pair.into();

        assert_eq!(vec, vec![11, 22]);
    }

    // =========================================================================
    // Edge Cases and Type Variations
    // =========================================================================

    #[test]
    fn works_with_strings() {
        let pair = Pair::new("apple".to_string(), "zebra".to_string()).unwrap();
        assert_eq!(pair.0, "apple");
        assert_eq!(pair.1, "zebra");
    }

    #[test]
    fn works_with_chars() {
        let pair = Pair::new('z', 'a').unwrap();
        // Should normalize to `(a, z)`
        assert_eq!(pair.0, 'a');
        assert_eq!(pair.1, 'z');
    }

    #[test]
    fn clone_works() {
        let pair1 = Pair::new("Plaid".to_owned(), "Stripes".to_owned()).unwrap();
        let pair2 = pair1.clone();

        assert_eq!(pair1, pair2);
    }

    #[test]
    fn copy_works_for_copy_types() {
        let pair1 = Pair::new(1, 2).unwrap();
        let pair2 = pair1; // Should copy, not move

        // Both should still be usable
        assert_eq!(pair1.0, 1);
        assert_eq!(pair2.0, 1);
    }
}
