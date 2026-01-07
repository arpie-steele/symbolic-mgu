//! Term enumeration for automated search.
//!
//! This module provides tools for systematically generating all
//! possible Terms with a fixed vocabulary up to a specified depth,
//! useful for exhaustive search, counterexample finding, and
//! automated theorem discovery.
//!
//! # Warning
//!
//! The number of terms grows **exponentially** with depth. Even
//! with modest parameters (e.g., 3 variables at depth 3), millions
//! of terms can be generated. Always use a depth limit or other
//! plan to prevent memory exhaustion.

use crate::{Metavariable, MguError, Node, Term, TermFactory, Type, TypeFactory};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

/// Iterator over all valid depth combinations for a given arity and maximum depth.
///
/// Generates all vectors of length `arity` where each element is in `0..depth`
/// and at least one element equals `depth - 1`.
///
/// # Purpose
///
/// When building terms at depth `d`, we need to combine sub-terms of depths
/// `0..d`. This iterator ensures we only generate combinations where at least
/// one child has depth `d-1`, preventing redundant generation of terms that
/// would have already been produced at an earlier depth.
///
/// # Example
///
/// For a binary operator (arity 2) at depth 2:
/// ```text
/// [0, 1] - first child from depth 0, second from depth 1
/// [1, 0] - first child from depth 1, second from depth 0
/// [1, 1] - both children from depth 1
/// ```
/// Note: `[0, 0]` is excluded because it would produce a term of depth 0,
/// which was already generated earlier.
#[derive(Debug, Clone)]
pub struct DepthCombinationIterator {
    /// The size of the resulting arrays.
    arity: usize,
    /// One more than the largest element of any returned vector.
    depth: usize,
    /// The current vector.
    current: Option<Vec<usize>>,
    /// End of work marker.
    done: bool,
}

impl DepthCombinationIterator {
    /// Create a new depth combination iterator.
    ///
    /// Returns an iterator over all valid depth assignments for `arity` slots
    /// where each depth is in `0..depth` and at least one equals `depth - 1`.
    #[must_use]
    pub fn new(arity: usize, depth: usize) -> Self {
        if arity == 0 || depth == 0 {
            Self {
                arity,
                depth,
                current: None,
                done: true,
            }
        } else {
            // Start with all zeros - this won't be valid (no depth-1), so first next() will advance
            Self {
                arity,
                depth,
                current: Some(vec![0; arity]),
                done: false,
            }
        }
    }

    /// Advance to the next combination, returns true if successful.
    ///
    /// Increments the current combination like a counter in base `depth`,
    /// moving from right to left with carry propagation.
    fn advance(&mut self) -> bool {
        if self.done {
            return false;
        }

        let current = match &mut self.current {
            Some(c) => c,
            None => {
                self.done = true;
                return false;
            }
        };

        // Increment like a counter in base `depth`
        let mut carry = true;
        for i in (0..self.arity).rev() {
            if carry {
                current[i] += 1;
                if current[i] >= self.depth {
                    current[i] = 0;
                } else {
                    carry = false;
                }
            }
        }

        if carry {
            // Overflowed - we're done
            self.done = true;
            false
        } else {
            true
        }
    }
}

impl Iterator for DepthCombinationIterator {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // Check current state first, then advance
        loop {
            // Check if current combination is valid (has at least one depth-1)
            if let Some(ref combo) = self.current {
                if combo.iter().any(|&d| d == self.depth - 1) {
                    let result = combo.clone();
                    // Advance for next call
                    self.advance();
                    return Some(result);
                }
            }

            // Current not valid or None, try to advance
            if !self.advance() {
                return None;
            }
        }
    }
}

/// Shared state for term search operations.
///
/// This structure holds all the static information needed to generate terms:
/// the available variables, nodes, types, and their relationships. It also
/// maintains a cache of iterators for different (type, depth) combinations
/// to avoid redundant work.
///
/// # Design
///
/// The state is wrapped in `Rc` and shared among multiple iterators. Each
/// iterator holds a `Weak` reference to prevent circular ownership. The
/// cache uses `RefCell` for interior mutability since iterators need to
/// clone themselves from the cache during operation.
///
/// # Sub-type Handling
///
/// The `subtypes_of` map is pre-computed during construction. For each type T,
/// it stores all types S where `S.is_subtype_of(T)`. This enables efficient
/// lookup when filling slots that accept a given type - we can use any
/// compatible sub-type.
#[derive(Debug)]
pub struct TermSearchStaticState<Ty, V, N, T, TF, TyF> {
    /// A factor to generate Term items.
    factory: TF,
    /// An ordered vector of unique Types seen for Nodes and Metavariables.
    types: Vec<Ty>,
    /// Lists of Metavariables listed by Type.
    vars_by_type: HashMap<Ty, Vec<V>>,
    /// Lists of Nodes listed by Type and arity.
    nodes_by_type_and_arity: HashMap<(Ty, usize), Vec<N>>,
    /// For each type, store all types that are sub-types of it (including itself)
    subtypes_of: HashMap<Ty, Vec<Ty>>,
    /// Cached iterators by (type, depth)
    prior_depths: TSIteratorCache<Ty, V, N, T, TF, TyF>,
}

/// A Cache of iterators with a key of Type and maximum depth.
type TSIteratorCache<Ty, V, N, T, TF, TyF> =
    RefCell<HashMap<(Ty, usize), TermSearchIterator<Ty, V, N, T, TF, TyF>>>;

/// Iterator over all terms of a given type up to a specified depth.
///
/// This enum represents two different iteration strategies:
/// - `PassZero`: For depth 0 (leaves only: variables and nullary nodes)
/// - `PassN`: For depth ≥ 1 (composite terms built from operators and sub-terms)
///
/// # Iteration Strategy
///
/// The iterator generates terms in a systematic order:
/// 1. At depth 0: variables first, then nullary nodes
/// 2. At depth N > 0: all ways to combine operators with sub-terms from depths 0..N
///
/// # Implementation Note
///
/// The `PassN` variant implements a complex state machine that iterates through:
/// - All operators of the target type
/// - All valid depth combinations for each operator's children
/// - All valid sub-terms for each depth/type combination
/// - All sub-types that can fill each slot
///
/// This results in a multi-level nested iteration that's managed explicitly
/// through the state fields.
#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum TermSearchIterator<Ty, V, N, T, TF, TyF> {
    /// Iterator over leaf-like terms of a specific type (depth 0).
    ///
    /// Produces terms in this order:
    /// 1. All variables of the requested type
    /// 2. All nullary nodes of the requested type
    ///
    /// # Fields
    ///
    /// - `search`: Weak reference to shared state
    /// - `term_type`: The type of terms to generate
    /// - `vars_done`: Have we finished iterating variables?
    /// - `nodes_done`: Have we finished iterating nullary nodes?
    /// - `sub_index`: Current position in the variable or node list
    PassZero {
        /// Weak reference to shared search state
        search: Weak<TermSearchStaticState<Ty, V, N, T, TF, TyF>>,
        /// Type of terms to generate
        term_type: Ty,
        /// Have we finished iterating nullary nodes?
        nodes_done: bool,
        /// Have we finished iterating variables?
        vars_done: bool,
        /// Current index in variable or node list
        sub_index: usize,
    },
    /// Iterator over composite terms up to depth `depth` (depth ≥ 1).
    ///
    /// Generates all terms that can be formed by applying operators to
    /// sub-terms of lesser depth. Implements a multi-level state machine:
    ///
    /// 1. **Operator iteration**: Try each operator (node) of the target type
    /// 2. **Depth combination**: For each operator, try all valid ways to
    ///    assign depths to its children (via `DepthCombinationIterator`)
    /// 3. **Sub-type iteration**: For each child slot, try all compatible sub-types
    /// 4. **Term iteration**: For each sub-type, iterate through all terms at
    ///    the assigned depth
    ///
    /// # Fields
    ///
    /// - `search`: Weak reference to shared state
    /// - `term_type`: The type of terms to generate
    /// - `depth`: Maximum depth for generated terms
    /// - `done`: Has iteration completed?
    /// - `key_iterator`: Iterates over (type, arity) pairs for operators
    /// - `current_key`: Current (type, arity) being processed
    /// - `node_iterator`: Iterates over nodes matching current key
    /// - `current_node`: Current operator being used to build terms
    /// - `current_arity`: Arity of current operator
    /// - `current_slot_types`: Type required for each child slot
    /// - `depths_iterator`: Generates valid depth combinations for children
    /// - `current_depths`: Current depth assignment for children
    /// - `child_slot_state`: For each child: (`current_term`, `subtype_iterators`, `current_iterator_index`)
    ///   Implements a generalized odometer/counter for Cartesian product iteration
    PassN {
        /// Weak reference to shared search state
        search: Weak<TermSearchStaticState<Ty, V, N, T, TF, TyF>>,
        /// Type of terms to generate
        term_type: Ty,
        /// Maximum depth for generated terms
        depth: usize,
        /// Has iteration completed?
        done: bool,
        /// Iterator over (type, arity) pairs
        key_iterator: std::vec::IntoIter<(Ty, usize)>,
        /// Current (type, arity) being processed
        current_key: Option<(Ty, usize)>,
        /// Iterator over nodes matching current key
        node_iterator: Option<std::vec::IntoIter<N>>,
        /// Current operator node
        current_node: Option<N>,
        /// Arity of current operator
        current_arity: Option<usize>,
        /// Type required for each child slot
        current_slot_types: Option<Vec<Ty>>,
        /// Generates valid depth combinations
        depths_iterator: Option<DepthCombinationIterator>,
        /// Current depth assignment for children
        current_depths: Option<Vec<usize>>,
        /// For each child slot: (`current_term`, `list_of_iterators_for_subtypes`, `current_iterator_index`)
        /// We iterate through sub-types, and for each sub-type we iterate through its terms
        child_slot_state: ChildSlotsState<Ty, V, N, T, TF, TyF>,
    },
}

/// Optional vectors of triples to keep track of state as we iterate.
type ChildSlotsState<Ty, V, N, T, TF, TyF> = Option<
    Vec<(
        Option<T>,
        Vec<TermSearchIterator<Ty, V, N, T, TF, TyF>>,
        usize,
    )>,
>;

impl<Ty, V, N, T, TF, TyF> TermSearchStaticState<Ty, V, N, T, TF, TyF>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF>,
    TyF: TypeFactory<Type = Ty>,
{
    /// Create a new term search state from a factory, nodes, and variables.
    ///
    /// This constructor:
    /// 1. Deduplicates and sorts variables by type
    /// 2. Deduplicates and sorts nodes by (type, arity)
    /// 3. Collects all unique types from variables and nodes
    /// 4. Pre-computes the sub-type relation for efficient lookup
    ///
    /// # Errors
    ///
    /// Returns an error if any metavariable's `get_type()` method fails, or if any
    /// node's `get_type()` or `get_arity()` methods fail. Current implementations
    /// (e.g., `WideMetavariable`, `BooleanSimpleNode`) never fail, but future
    /// database-backed implementations may return errors.
    ///
    /// # Returns
    ///
    /// An `Rc<Self>` suitable for sharing among multiple iterators.
    pub fn new(factory: TF, node_list: &[N], var_list: &[V]) -> Result<Rc<Self>, MguError> {
        let mut t_set = HashSet::new();
        let mut v_map: HashMap<Ty, HashSet<&V>> = HashMap::new();
        let mut n_map: HashMap<(Ty, usize), HashSet<&N>> = HashMap::new();

        // First gather `v_map` as map to sets, then finalize as map to sorted vector of unique variables
        for v in var_list {
            let t = v.get_type()?;
            t_set.insert(t.clone());
            v_map.entry(t).or_default().insert(v);
        }
        let v_map = v_map
            .into_iter()
            .map(|(t, s)| {
                let mut v = s.into_iter().cloned().collect::<Vec<_>>();
                v.sort();
                (t, v)
            })
            .collect();

        // First gather `n_map` as map to sets, then finalize as map to sorted vector of unique nodes
        for n in node_list {
            let t = n.get_type()?;
            let a = n.get_arity()?;
            let key = (t.clone(), a);
            t_set.insert(t.clone());

            n_map.entry(key).or_default().insert(n);
        }
        let n_map = n_map
            .into_iter()
            .map(|(t, s)| {
                let mut v = s.into_iter().cloned().collect::<Vec<_>>();
                v.sort();
                (t, v)
            })
            .collect();

        // Finalize `t_vec` as sorted vector of unique types of variables and nodes
        let mut t_vec = t_set.into_iter().collect::<Vec<_>>();
        t_vec.sort();

        // Pre-compute sub-type relations: for each type, find all types that are sub-types of it
        let mut subtypes_map: HashMap<Ty, Vec<Ty>> = HashMap::new();
        for super_type in &t_vec {
            let mut subtypes = Vec::new();
            for sub_type in &t_vec {
                if sub_type.is_subtype_of(super_type) {
                    subtypes.push(sub_type.clone());
                }
            }
            subtypes.sort();
            subtypes_map.insert(super_type.clone(), subtypes);
        }

        Ok(Rc::new(Self {
            factory,
            types: t_vec,
            vars_by_type: v_map,
            nodes_by_type_and_arity: n_map,
            subtypes_of: subtypes_map,
            prior_depths: RefCell::new(HashMap::new()),
        }))
    }

    /// Get a reference to the term factory.
    #[must_use]
    pub fn get_term_factory(&self) -> &TF {
        &self.factory
    }

    /// Get all types present in the variable and node lists.
    #[must_use]
    pub fn get_types(&self) -> &[Ty] {
        &self.types
    }

    /// Get all types that are sub-types of `slot_type`.
    ///
    /// Returns types that can be used in a slot requiring `slot_type`,
    /// including `slot_type` itself if it appears in the type list.
    #[must_use]
    pub fn get_types_by_slot_type(&self, slot_type: &Ty) -> Vec<Ty> {
        self.types
            .iter()
            .filter(|&t| t.is_subtype_of(slot_type))
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Get all variables of exactly the specified type.
    #[must_use]
    pub fn get_vars(&self, exact_type: &Ty) -> &[V] {
        if let Some(vars) = self.vars_by_type.get(exact_type) {
            vars
        } else {
            &[]
        }
    }

    /// Get all variables whose types appear in `exact_types`, deduplicated and sorted.
    #[must_use]
    pub fn get_vars_by_types(&self, exact_types: &[Ty]) -> Vec<V> {
        let type_set = exact_types.iter().collect::<HashSet<_>>();
        let mut type_list = type_set.into_iter().collect::<Vec<_>>();
        type_list.sort();
        let mut var_list = Vec::new();
        for type_key in type_list {
            for v in self.get_vars(type_key) {
                var_list.push(v.clone());
            }
        }
        var_list
    }

    /// Get all variables that can fill a slot of type `slot_type`.
    ///
    /// This includes variables of all sub-types of `slot_type`.
    #[must_use]
    pub fn get_vars_by_slot_type(&self, slot_type: &Ty) -> Vec<V> {
        let wanted_types = self.get_types_by_slot_type(slot_type);
        self.get_vars_by_types(&wanted_types)
    }

    /// Get all nodes of exactly the specified type and arity.
    #[must_use]
    pub fn get_nodes(&self, exact_type: &Ty, arity: usize) -> &[N] {
        let key = (exact_type.clone(), arity);

        if let Some(nodes) = self.nodes_by_type_and_arity.get(&key) {
            nodes
        } else {
            &[]
        }
    }

    /// Get all (type, arity) keys matching a predicate.
    ///
    /// Used internally to filter nodes by criteria like "nullary only"
    /// or "specific type only".
    #[must_use]
    pub fn get_node_keys_by_filter<F>(&self, filter: F) -> Vec<(Ty, usize)>
    where
        F: Fn(&Ty, usize) -> bool,
    {
        self.nodes_by_type_and_arity
            .keys()
            .filter(|(t, a)| filter(t, *a))
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Get all nodes matching any of the given (type, arity) pairs, deduplicated and sorted.
    #[must_use]
    pub fn get_nodes_by_type_arity_pairs(&self, exact_keys: &[(Ty, usize)]) -> Vec<N> {
        let key_set = exact_keys.iter().collect::<HashSet<_>>();
        let mut key_list = key_set.into_iter().collect::<Vec<_>>();
        key_list.sort();
        let mut node_list = Vec::new();
        for key in key_list {
            for n in self.get_nodes(&key.0, key.1) {
                node_list.push(n.clone());
            }
        }
        node_list
    }

    /// Get all nullary nodes (arity 0) of exactly the specified type.
    #[must_use]
    pub fn get_nullary_nodes(&self, exact_type: &Ty) -> Vec<N> {
        let wanted_keys = self.get_node_keys_by_filter(|node_type, node_arity| {
            *node_type == *exact_type && node_arity == 0
        });
        self.get_nodes_by_type_arity_pairs(&wanted_keys)
    }

    /// Get all non-nullary nodes (arity > 0) of exactly the specified type.
    #[must_use]
    pub fn get_nonnullary_nodes(&self, exact_type: &Ty) -> Vec<N> {
        let wanted_keys = self.get_node_keys_by_filter(|node_type, node_arity| {
            *node_type == *exact_type && node_arity != 0
        });
        self.get_nodes_by_type_arity_pairs(&wanted_keys)
    }

    /// Get all nullary nodes whose types appear in `exact_types`.
    #[must_use]
    pub fn get_nullary_nodes_by_types(&self, exact_types: &[Ty]) -> Vec<N> {
        let type_set = exact_types.iter().cloned().collect::<HashSet<_>>();
        let wanted_keys = self.get_node_keys_by_filter(|node_type, node_arity| {
            type_set.contains(node_type) && node_arity == 0
        });
        self.get_nodes_by_type_arity_pairs(&wanted_keys)
    }

    /// Get all non-nullary nodes whose types appear in `exact_types`.
    #[must_use]
    pub fn get_nonnullary_nodes_by_types(&self, exact_types: &[Ty]) -> Vec<N> {
        let type_set = exact_types.iter().cloned().collect::<HashSet<_>>();
        let wanted_keys = self.get_node_keys_by_filter(|node_type, node_arity| {
            type_set.contains(node_type) && node_arity != 0
        });
        self.get_nodes_by_type_arity_pairs(&wanted_keys)
    }

    /// Get all nullary nodes that can fill a slot of type `slot_type`.
    #[must_use]
    pub fn get_nullary_nodes_by_slot_type(&self, slot_type: &Ty) -> Vec<N> {
        let wanted_types = self.get_types_by_slot_type(slot_type);
        self.get_nullary_nodes_by_types(&wanted_types)
    }

    /// Get all non-nullary nodes that can fill a slot of type `slot_type`.
    #[must_use]
    pub fn get_nonnullary_nodes_by_slot_type(&self, slot_type: &Ty) -> Vec<N> {
        let wanted_types = self.get_types_by_slot_type(slot_type);
        self.get_nonnullary_nodes_by_types(&wanted_types)
    }
}

/// Get or create an iterator for terms of a given type and maximum depth.
///
/// This function uses memoization: if an iterator for (`term_type`, `max_depth`) already
/// exists in the cache, it returns a clone. Otherwise, it ensures all iterators for
/// lesser depths exist, creates the new iterator, caches it, and returns a clone.
///
/// # Errors
///
/// Propagates any errors from [`TermSearchIterator::new_at_depth`]. Currently never
/// fails with standard implementations, but future database-backed implementations
/// may return errors.
pub fn get_iterator<Ty, V, N, T, TF, TyF>(
    rc_state: &Rc<TermSearchStaticState<Ty, V, N, T, TF, TyF>>,
    term_type: Ty,
    max_depth: usize,
) -> Result<TermSearchIterator<Ty, V, N, T, TF, TyF>, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermMetavariable = V, TermNode = N>,
    TyF: TypeFactory<Type = Ty>,
{
    // Check if the requested iterator already exists
    let key = (term_type.clone(), max_depth);
    {
        let cache = rc_state.prior_depths.borrow();
        if let Some(iter) = cache.get(&key) {
            return Ok(iter.clone());
        }
    }

    // Ensure all iterators for ( ..., d) where d < `max_depth` exist
    for depth in 0..max_depth {
        for key_type in rc_state.types.iter() {
            let sub_key = (key_type.clone(), depth);
            let needs_creation = !rc_state.prior_depths.borrow().contains_key(&sub_key);

            if needs_creation {
                let new_iter = TermSearchIterator::new_at_depth(rc_state, key_type.clone(), depth)?;
                rc_state.prior_depths.borrow_mut().insert(sub_key, new_iter);
            }
        }
    }

    // Create the new iterator for `(term_type, max_depth)`
    let new_iter = TermSearchIterator::new_at_depth(rc_state, term_type.clone(), max_depth)?;
    rc_state
        .prior_depths
        .borrow_mut()
        .insert(key.clone(), new_iter.clone());

    Ok(new_iter)
}

impl<Ty, V, N, T, TF, TyF> TermSearchIterator<Ty, V, N, T, TF, TyF>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermMetavariable = V, TermNode = N>,
    TyF: TypeFactory<Type = Ty>,
{
    /// Create a new iterator for terms of `term_type` at exactly `depth`.
    ///
    /// # Depth Semantics
    ///
    /// - Depth 0: Variables and nullary nodes only
    /// - Depth N > 0: Terms with maximum tree depth N (at least one path
    ///   from root to leaf has length N)
    ///
    /// # Note
    ///
    /// Prefer using [`get_iterator`] instead, which handles caching and
    /// ensures all prerequisite iterators exist.
    ///
    /// # Errors
    ///
    /// Currently never returns an error. The `Result` return type is reserved for
    /// future implementations that may need to perform fallible operations (e.g.,
    /// database queries).
    pub fn new_at_depth(
        rc_state: &Rc<TermSearchStaticState<Ty, V, N, T, TF, TyF>>,
        term_type: Ty,
        depth: usize,
    ) -> Result<Self, MguError> {
        if depth == 0 {
            Ok(TermSearchIterator::PassZero {
                search: Rc::downgrade(rc_state),
                term_type,
                nodes_done: false,
                vars_done: false,
                sub_index: 0,
            })
        } else {
            // Get all nodes of the specified type with non-zero arity
            let mut keys: Vec<(Ty, usize)> = rc_state
                .nodes_by_type_and_arity
                .keys()
                .filter(|(node_type, arity)| *arity != 0 && node_type == &term_type)
                .cloned()
                .collect();
            keys.sort(); // Ensure deterministic iteration order

            Ok(TermSearchIterator::PassN {
                search: Rc::downgrade(rc_state),
                term_type,
                depth,
                done: false,
                key_iterator: keys.into_iter(),
                current_key: None,
                node_iterator: None,
                current_node: None,
                current_arity: None,
                current_slot_types: None,
                depths_iterator: None,
                current_depths: None,
                child_slot_state: None,
            })
        }
    }
}

impl<Ty, V, N, T, TF, TyF> Clone for TermSearchIterator<Ty, V, N, T, TF, TyF>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
{
    /// Clone the iterator, resetting it to the beginning.
    ///
    /// For `PassZero`, cloning preserves state exactly. For `PassN`, cloning
    /// creates a fresh iterator starting from the beginning (state is too
    /// complex to clone safely, and we need fresh iterators for the cache anyway).
    fn clone(&self) -> Self {
        match self {
            TermSearchIterator::PassZero {
                search,
                term_type,
                nodes_done,
                vars_done,
                sub_index,
            } => TermSearchIterator::PassZero {
                search: search.clone(),
                term_type: term_type.clone(),
                nodes_done: *nodes_done,
                vars_done: *vars_done,
                sub_index: *sub_index,
            },
            TermSearchIterator::PassN {
                search,
                term_type,
                depth,
                done,
                key_iterator: _,
                current_key: _,
                node_iterator: _,
                current_node: _,
                current_arity: _,
                current_slot_types: _,
                depths_iterator: _,
                current_depths: _,
                child_slot_state: _,
            } => {
                // For `PassN`, we need to reconstruct a fresh iterator from scratch
                // Get the search state to rebuild the keys
                let mut keys = if let Some(search_state) = search.upgrade() {
                    search_state
                        .nodes_by_type_and_arity
                        .keys()
                        .filter(|(node_type, arity)| *arity != 0 && node_type == term_type)
                        .cloned()
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                keys.sort(); // Ensure deterministic iteration order

                TermSearchIterator::PassN {
                    search: search.clone(),
                    term_type: term_type.clone(),
                    depth: *depth,
                    done: *done || keys.is_empty(),
                    key_iterator: keys.into_iter(),
                    current_key: None, // Reset to start
                    node_iterator: None,
                    current_node: None,
                    current_arity: None,
                    current_slot_types: None,
                    depths_iterator: None,
                    current_depths: None,
                    child_slot_state: None,
                }
            }
        }
    }
}

impl<Ty, V, N, T, TF, TyF> Iterator for TermSearchIterator<Ty, V, N, T, TF, TyF>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TyF, Term = T, TermMetavariable = V, TermNode = N>,
    TyF: TypeFactory<Type = Ty>,
{
    type Item = T;

    /// Get the next term from the iterator.
    ///
    /// Returns `None` when all terms at this depth have been generated.
    /// The implementation is a large state machine that manages multiple
    /// levels of nested iteration.
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TermSearchIterator::PassZero {
                search,
                term_type,
                nodes_done,
                vars_done,
                sub_index,
            } => {
                let search_state = search.upgrade()?;

                loop {
                    if *vars_done && *nodes_done {
                        return None;
                    }

                    // Phase 1: Iterate over variables of the requested type
                    if !*vars_done {
                        let current_vars = search_state.vars_by_type.get(term_type);
                        if let Some(current_vec) = current_vars {
                            if *sub_index < current_vec.len() {
                                let v = current_vec[*sub_index].clone();
                                *sub_index += 1;
                                return search_state.factory.create_leaf(v).ok();
                            }
                        }
                        // Done with vars, move to nodes
                        *vars_done = true;
                        *sub_index = 0;
                        continue;
                    }

                    // Phase 2: Iterate over nullary nodes of the requested type
                    if !*nodes_done {
                        let key = (term_type.clone(), 0usize);
                        let current_nodes = search_state.nodes_by_type_and_arity.get(&key);
                        if let Some(current_vec) = current_nodes {
                            if *sub_index < current_vec.len() {
                                let n = current_vec[*sub_index].clone();
                                *sub_index += 1;
                                return search_state.factory.create_node(n, Vec::new()).ok();
                            }
                        }
                        // Done with nodes
                        *nodes_done = true;
                    }
                }
            }
            TermSearchIterator::PassN {
                search,
                term_type: _,
                depth,
                done,
                key_iterator,
                current_key,
                node_iterator,
                current_node,
                current_arity,
                current_slot_types,
                depths_iterator,
                current_depths,
                child_slot_state,
            } => {
                let search_state = match search.upgrade() {
                    Some(s) => s,
                    None => {
                        *done = true;
                        return None;
                    }
                };

                // The `PassN` state machine has 5 nested levels:
                // 1. Iterate over (type, arity) keys
                // 2. Iterate over nodes for current key
                // 3. Iterate over depth combinations for current node
                // 4. For each slot, iterate over compatible sub-types
                // 5. For each sub-type, iterate over terms at the assigned depth
                //
                // The state is advanced like a generalized odometer, with
                // carries propagating from innermost to outermost level.
                loop {
                    if *done {
                        return None;
                    }

                    // Level 1: Get the next (Type, arity) key if needed
                    if current_key.is_none() {
                        match key_iterator.next() {
                            Some(key) => {
                                *current_key = Some(key.clone());
                                *node_iterator = None;
                                *current_node = None;
                            }
                            None => {
                                *done = true;
                                return None;
                            }
                        }
                    }

                    // Level 2: Get the next node for the current key if needed
                    if current_node.is_none() {
                        if node_iterator.is_none() {
                            let key = current_key.as_ref().unwrap();
                            if let Some(nodes) = search_state.nodes_by_type_and_arity.get(key) {
                                *node_iterator = Some(nodes.clone().into_iter());
                            } else {
                                // No nodes for this key, move to next key
                                *current_key = None;
                                continue;
                            }
                        }

                        if let Some(ref mut iter) = node_iterator {
                            match iter.next() {
                                Some(node) => {
                                    let arity = match node.get_arity() {
                                        Ok(a) => a,
                                        Err(_) => {
                                            continue;
                                        }
                                    };

                                    // Get slot types for this node
                                    let mut slot_types = Vec::with_capacity(arity);
                                    let mut error = false;
                                    for i in 0..arity {
                                        match node.get_slot_type(i) {
                                            Ok(ty) => slot_types.push(ty),
                                            Err(_) => {
                                                error = true;
                                                break;
                                            }
                                        }
                                    }

                                    if error {
                                        continue;
                                    }

                                    *current_node = Some(node);
                                    *current_arity = Some(arity);
                                    *current_slot_types = Some(slot_types);
                                    *depths_iterator =
                                        Some(DepthCombinationIterator::new(arity, *depth));
                                    *current_depths = None;
                                    *child_slot_state = None;
                                }
                                None => {
                                    *current_key = None;
                                    *node_iterator = None;
                                    continue;
                                }
                            }
                        }
                    }

                    // Level 3: Get the next depth combination if needed
                    if current_depths.is_none() {
                        if let Some(ref mut depth_iter) = depths_iterator {
                            match depth_iter.next() {
                                Some(depths) => {
                                    *current_depths = Some(depths);
                                    *child_slot_state = None;
                                }
                                None => {
                                    *current_node = None;
                                    *depths_iterator = None;
                                    continue;
                                }
                            }
                        } else {
                            *current_node = None;
                            continue;
                        }
                    }

                    // Level 4 & 5: Initialize child slot state if needed
                    // This sets up iterators for all sub-types of each slot type,
                    // creating a Cartesian product iteration structure.
                    if child_slot_state.is_none() {
                        let depths = current_depths.as_ref().unwrap();
                        let slot_types = current_slot_types.as_ref().unwrap();
                        let arity = *current_arity.as_ref().unwrap();

                        let mut slots = Vec::with_capacity(arity);
                        let mut init_failed = false;

                        for i in 0..arity {
                            let slot_type = &slot_types[i];
                            let child_depth = depths[i];

                            // Get all sub-types that can fill this slot
                            let subtypes = match search_state.subtypes_of.get(slot_type) {
                                Some(st) => st,
                                None => {
                                    init_failed = true;
                                    break;
                                }
                            };

                            // Create iterators for each sub-type
                            let mut subtype_iters = Vec::new();
                            for subtype in subtypes {
                                match get_iterator(&search_state, subtype.clone(), child_depth) {
                                    Ok(iter) => subtype_iters.push(iter),
                                    Err(_) => continue,
                                }
                            }

                            if subtype_iters.is_empty() {
                                init_failed = true;
                                break;
                            }

                            // Initialize: no current term, iterators ready, start at index 0
                            slots.push((None, subtype_iters, 0));
                        }

                        if init_failed {
                            *current_depths = None;
                            continue;
                        }

                        *child_slot_state = Some(slots);

                        // Prime the pump: get the first term for each slot
                        let need_advance = child_slot_state.as_mut().unwrap();
                        let mut advance_failed = false;
                        for slot in need_advance.iter_mut() {
                            if slot.0.is_none() {
                                // Try to get first term from first iterator
                                if let Some(iter) = slot.1.get_mut(slot.2) {
                                    slot.0 = iter.next();
                                }
                                if slot.0.is_none() {
                                    advance_failed = true;
                                    break;
                                }
                            }
                        }

                        if advance_failed {
                            *current_depths = None;
                            *child_slot_state = None;
                            continue;
                        }
                    }

                    // Build and return the term with current child terms
                    let children = if let Some(ref state) = child_slot_state {
                        // Collect current terms from each slot
                        let mut children = Vec::with_capacity(state.len());
                        let mut has_none = false;
                        for slot in state {
                            match &slot.0 {
                                Some(term) => children.push(term.clone()),
                                None => {
                                    has_none = true;
                                    break;
                                }
                            }
                        }

                        if has_none {
                            // Should not happen after initialization
                            *current_depths = None;
                            *child_slot_state = None;
                            continue;
                        }
                        children
                    } else {
                        continue;
                    };

                    {
                        // Build the term
                        let node = current_node.as_ref().unwrap().clone();
                        let result = search_state.factory.create_node(node, children);

                        // Advance to next combination (like incrementing a multi-digit counter).
                        // We iterate through all combinations of (sub-type, term) for each slot,
                        // treating this as a mixed-radix number where each position can have
                        // a different base.
                        let slots = child_slot_state.as_mut().unwrap();
                        let mut carry = true;
                        for i in (0..slots.len()).rev() {
                            if !carry {
                                break;
                            }

                            // Extract current index to avoid borrow checker issues
                            let current_idx = slots[i].2;

                            // Try to advance the current sub-type's iterator
                            if let Some(iter) = slots[i].1.get_mut(current_idx) {
                                slots[i].0 = iter.next();
                            }

                            if slots[i].0.is_some() {
                                // Got a term, no carry needed
                                carry = false;
                            } else {
                                // Current sub-type iterator exhausted, try next sub-type
                                slots[i].2 += 1;
                                let next_idx = slots[i].2;
                                if next_idx < slots[i].1.len() {
                                    if let Some(iter) = slots[i].1.get_mut(next_idx) {
                                        slots[i].0 = iter.next();
                                        if slots[i].0.is_some() {
                                            carry = false;
                                        }
                                    }
                                }

                                if carry {
                                    // All sub-types exhausted for this slot, reset to beginning.
                                    // Get fresh clones of all sub-type iterators for this slot.
                                    let slot_type = &current_slot_types.as_ref().unwrap()[i];
                                    let child_depth = current_depths.as_ref().unwrap()[i];
                                    let subtypes = search_state.subtypes_of.get(slot_type).unwrap();

                                    let mut fresh_iters = Vec::new();
                                    for subtype in subtypes {
                                        if let Ok(iter) = get_iterator(
                                            &search_state,
                                            subtype.clone(),
                                            child_depth,
                                        ) {
                                            fresh_iters.push(iter);
                                        }
                                    }

                                    // Replace the exhausted iterators with fresh ones
                                    slots[i].1 = fresh_iters;
                                    slots[i].2 = 0;

                                    // Get the first term from the fresh iterator
                                    if let Some(iter) = slots[i].1.get_mut(0) {
                                        slots[i].0 = iter.next();
                                    }
                                    // If still None, we're truly exhausted - carry continues
                                }
                            }
                        }

                        if carry {
                            // Exhausted all combinations for this depth combination
                            *current_depths = None;
                            *child_slot_state = None;
                        }

                        // Return the term we built (if successful)
                        match result {
                            Ok(term) => return Some(term),
                            Err(_) => continue, // Skip this combination, try next
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        EnumTerm, EnumTermFactory, MetavariableFactory, MguError, NodeByte, SimpleType,
        SimpleTypeFactory, WideMetavariable, WideMetavariableFactory,
    };

    type TestVar = WideMetavariable;
    type TestTerm = EnumTerm<SimpleType, TestVar, NodeByte>;
    type TestFactory = EnumTermFactory<SimpleType, TestVar, NodeByte, SimpleTypeFactory>;
    type TestState = Rc<
        TermSearchStaticState<
            SimpleType,
            TestVar,
            NodeByte,
            TestTerm,
            TestFactory,
            SimpleTypeFactory,
        >,
    >;

    fn create_simple_state(
        n_bools: usize,
        n_sets: usize,
        n_classes: usize,
    ) -> Result<TestState, MguError> {
        let vf = WideMetavariableFactory::new(SimpleTypeFactory);
        use SimpleType::*;
        let some_vars = vf
            .list_metavariables_by_type(&Boolean)
            .take(n_bools)
            .chain(vf.list_metavariables_by_type(&Setvar).take(n_sets))
            .chain(vf.list_metavariables_by_type(&Class).take(n_classes))
            .collect::<Vec<_>>();
        use NodeByte::*;
        let some_nodes = vec![Not, Implies, ForAll, IsElementOf, True, False, UniversalCls];
        let tf: TestFactory = EnumTermFactory::new(SimpleTypeFactory);
        TermSearchStaticState::new(tf, &some_nodes, &some_vars)
    }

    #[test]
    fn search_static_state_all_types() {
        use SimpleType::*;
        let rc_state = create_simple_state(3, 3, 3).unwrap();
        assert_eq!(rc_state.get_types(), &[Boolean, Setvar, Class]);

        for t1 in rc_state.get_types() {
            let st = rc_state.subtypes_of.get(t1);
            if let Some(st) = st {
                for t2 in rc_state.get_types() {
                    let found = st.contains(t2);
                    let expected = t2.is_subtype_of(t1);
                    assert_eq!(found, expected, "{t2} is_substype_of {t1}");
                }
            } else {
                assert!(st.is_some(), "substypes_of {} not defined.", t1);
            }
        }

        let rc_state = create_simple_state(0, 0, 0).unwrap();
        assert_eq!(rc_state.get_types(), &[Boolean, Class]);

        for t1 in rc_state.get_types() {
            let st = rc_state.subtypes_of.get(t1);
            if let Some(st) = st {
                for t2 in rc_state.get_types() {
                    let found = st.contains(t2);
                    let expected = t2.is_subtype_of(t1);
                    assert_eq!(found, expected, "{t2} is_substype_of {t1}");
                }
            } else {
                assert!(st.is_some(), "substypes_of {} not defined.", t1);
            }
        }
    }

    #[test]
    fn search_static_state_all_vars() {
        use SimpleType::*;
        let rc_state = create_simple_state(3, 3, 3).unwrap();
        assert_eq!(rc_state.get_types(), &[Boolean, Setvar, Class]);
        for t in rc_state.get_types() {
            let expected = 3;
            let vars = rc_state.get_vars(t).len();
            assert_eq!(
                vars, expected,
                "For type {t}, expected = {expected}, got = {vars}."
            )
        }

        let rc_state = create_simple_state(0, 1, 2).unwrap();
        assert_eq!(rc_state.get_types(), &[Boolean, Setvar, Class]);
        for (i, t) in rc_state.get_types().iter().enumerate() {
            let expected = i;
            let vars = rc_state.get_vars(t).len();
            assert_eq!(
                vars, expected,
                "For type {t}, expected = {expected}, got = {vars}."
            )
        }

        let rc_state = create_simple_state(2, 1, 0).unwrap();
        assert_eq!(rc_state.get_types(), &[Boolean, Setvar, Class]);
        for (i, t) in rc_state.get_types().iter().enumerate() {
            let expected = 2 - i;
            let vars = rc_state.get_vars(t).len();
            assert_eq!(
                vars, expected,
                "For type {t}, expected = {expected}, got = {vars}."
            )
        }
    }

    #[test]
    fn search_static_state_all_nodes() {
        use NodeByte::*;
        use SimpleType::*;
        let rc_state = create_simple_state(0, 0, 0).unwrap();
        let data: [(_, _, &[NodeByte]); 12] = [
            (Boolean, 0, &[False, True]),
            (Boolean, 1, &[Not]),
            (Boolean, 2, &[Implies, ForAll, IsElementOf]),
            (Boolean, 3, &[]),
            (Setvar, 0, &[]),
            (Setvar, 1, &[]),
            (Setvar, 2, &[]),
            (Setvar, 3, &[]),
            (Class, 0, &[UniversalCls]),
            (Class, 1, &[]),
            (Class, 2, &[]),
            (Class, 3, &[]),
        ];

        for (the_type, the_arity, expected) in data {
            let result = rc_state.get_nodes(&the_type, the_arity);
            assert_eq!(result, expected, "get_nodes({the_type}, {the_arity})")
        }

        for (i, (t1, a1, e1)) in data.iter().cloned().enumerate() {
            for (j, (t2, a2, e2)) in data.iter().cloned().enumerate() {
                if i == j {
                    continue;
                }
                let test = vec![(t1, a1), (t2, a2)];
                let expected = (if i < j {
                    e1.iter().cloned().chain(e2.iter().cloned())
                } else {
                    e2.iter().cloned().chain(e1.iter().cloned())
                })
                .collect::<Vec<_>>();
                let result = rc_state.get_nodes_by_type_arity_pairs(&test);
                assert_eq!(
                    &result, &expected,
                    "get_nodes_by_type_arity_pairs({:?})",
                    &test
                );
            }
        }
        assert_eq!(rc_state.get_nullary_nodes(&Boolean), vec![False, True]);
        assert_eq!(rc_state.get_nullary_nodes(&Setvar), vec![]);
        assert_eq!(rc_state.get_nullary_nodes(&Class), vec![UniversalCls]);

        assert_eq!(
            rc_state.get_nonnullary_nodes(&Boolean),
            vec![Not, Implies, ForAll, IsElementOf]
        );
        assert_eq!(rc_state.get_nonnullary_nodes(&Setvar), vec![]);
        assert_eq!(rc_state.get_nonnullary_nodes(&Class), vec![]);

        assert_eq!(
            rc_state.get_nullary_nodes_by_slot_type(&Boolean),
            vec![False, True]
        );
        assert_eq!(rc_state.get_nullary_nodes_by_slot_type(&Setvar), vec![]);
        assert_eq!(
            rc_state.get_nullary_nodes_by_slot_type(&Class),
            vec![UniversalCls]
        );

        assert_eq!(
            rc_state.get_nonnullary_nodes_by_slot_type(&Boolean),
            vec![Not, Implies, ForAll, IsElementOf]
        );
        assert_eq!(rc_state.get_nonnullary_nodes_by_slot_type(&Setvar), vec![]);
        assert_eq!(rc_state.get_nonnullary_nodes_by_slot_type(&Class), vec![]);
    }

    #[test]
    fn get_iterator_no_vars() {
        use NodeByte::*;
        use SimpleType::*;
        let rc_state = create_simple_state(0, 0, 0).unwrap();

        let results = get_iterator(&rc_state, Boolean, 0);
        assert!(
            results.is_ok(),
            "get_iterator(_, {}, {}).is_ok()",
            Boolean,
            0
        );
        let results = results.unwrap().collect::<Vec<_>>();
        assert!(
            results.iter().all(|x| !x.is_metavariable()),
            "get_iterator(_, {}, {}), None are variables.",
            Boolean,
            0
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(False, vec![])),
            "get_iterator(_, {}, {}) = {:?}, Found False.",
            Boolean,
            0,
            results
        );
        assert!(
            !results.contains(&EnumTerm::NodeOrLeaf(UniversalCls, vec![])),
            "get_iterator(_, {}, {}) = {:?}, Found False.",
            Boolean,
            0,
            results
        );
        assert!(
            results.iter().all(|x| matches!(x.get_type(), Ok(Boolean))),
            "get_iterator(_, {}, {}) = {:?}, All are {}.",
            Boolean,
            0,
            results,
            Boolean
        );
    }

    #[test]
    fn get_iterator_with_vars() {
        use NodeByte::*;
        use SimpleType::*;
        let rc_state = create_simple_state(3, 3, 3).unwrap();

        let results = get_iterator(&rc_state, Boolean, 0);
        assert!(
            results.is_ok(),
            "get_iterator(_, {}, {}).is_ok()",
            Boolean,
            0
        );
        let results = results.unwrap();
        assert!(matches!(
            &results,
            &TermSearchIterator::PassZero {
                search: _,
                term_type: _,
                nodes_done: false,
                vars_done: false,
                sub_index: 0
            }
        ));
        let results = results.collect::<Vec<_>>();
        assert!(
            !results.iter().all(|x| x.is_metavariable())
                && !results.iter().all(|x| !x.is_metavariable()),
            "get_iterator(_, {}, {}) = {:?}, Some are variables.",
            Boolean,
            0,
            results
        );
        assert!(
            results.contains(&EnumTerm::Leaf(
                WideMetavariable::try_from_type_and_index(Boolean, 0).unwrap()
            )),
            "get_iterator(_, {}, {}) = {:?}, Found V0.",
            Boolean,
            0,
            results
        );
        assert!(
            results.contains(&EnumTerm::Leaf(
                WideMetavariable::try_from_type_and_index(Boolean, 1).unwrap()
            )),
            "get_iterator(_, {}, {}) = {:?}, Found V1.",
            Boolean,
            0,
            results
        );
        assert!(
            results.contains(&EnumTerm::Leaf(
                WideMetavariable::try_from_type_and_index(Boolean, 2).unwrap()
            )),
            "get_iterator(_, {}, {}) = {:?}, Found V2.",
            Boolean,
            0,
            results
        );
        assert!(
            !results.contains(&EnumTerm::Leaf(
                WideMetavariable::try_from_type_and_index(Boolean, 3).unwrap()
            )),
            "get_iterator(_, {}, {}) = {:?}, Found V3.",
            Boolean,
            0,
            results
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(False, vec![])),
            "get_iterator(_, {}, {}) = {:?}, Found False.",
            Boolean,
            0,
            results
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(True, vec![])),
            "get_iterator(_, {}, {}), Found true.",
            Boolean,
            0
        );

        assert!(
            !results.contains(&EnumTerm::Leaf(
                WideMetavariable::try_from_type_and_index(Setvar, 0).unwrap()
            )),
            "get_iterator(_, {}, {}) = {:?}, Found V0.",
            Boolean,
            0,
            results
        );
        assert!(
            results.iter().all(|x| matches!(x.get_type(), Ok(Boolean))),
            "get_iterator(_, {}, {}) = {:?}, All are {}.",
            Boolean,
            0,
            results,
            Boolean
        );
    }

    #[test]
    fn depth_combination_iterator_arity1_depth1() {
        let iter = DepthCombinationIterator::new(1, 1);
        let results: Vec<Vec<usize>> = iter.collect();
        assert_eq!(
            results,
            vec![vec![0]],
            "Arity 1, depth 1 should produce [0]"
        );
    }

    #[test]
    fn depth_combination_iterator_arity2_depth1() {
        let iter = DepthCombinationIterator::new(2, 1);
        let results: Vec<Vec<usize>> = iter.collect();
        assert_eq!(
            results,
            vec![vec![0, 0]],
            "Arity 2, depth 1 should produce [0,0]"
        );
    }

    #[test]
    fn depth_combination_iterator_arity2_depth2() {
        let iter = DepthCombinationIterator::new(2, 2);
        let results: Vec<Vec<usize>> = iter.collect();
        assert_eq!(
            results,
            vec![vec![0, 1], vec![1, 0], vec![1, 1]],
            "Arity 2, depth 2 should produce [0,1], [1,0], [1,1]"
        );
    }

    #[test]
    fn depth_combination_iterator_arity3_depth2() {
        let iter = DepthCombinationIterator::new(3, 2);
        let results: Vec<Vec<usize>> = iter.collect();
        // All combinations with at least one 1
        assert_eq!(
            results.len(),
            7,
            "Arity 3, depth 2 should produce 7 combinations"
        );
        assert!(
            results.iter().all(|combo| combo.contains(&1)),
            "All combinations should have at least one depth-1"
        );
        assert!(
            results.iter().all(|combo| combo.iter().all(|&d| d < 2)),
            "All depths should be < 2"
        );
    }

    #[test]
    fn depth_combination_iterator_edge_cases() {
        // Zero arity should produce nothing
        let iter = DepthCombinationIterator::new(0, 1);
        let results: Vec<Vec<usize>> = iter.collect();
        assert_eq!(
            results,
            Vec::<Vec<usize>>::new(),
            "Arity 0 should produce nothing"
        );

        // Zero depth should produce nothing
        let iter = DepthCombinationIterator::new(2, 0);
        let results: Vec<Vec<usize>> = iter.collect();
        assert_eq!(
            results,
            Vec::<Vec<usize>>::new(),
            "Depth 0 should produce nothing"
        );
    }

    #[test]
    fn get_iterator_depth1_boolean() {
        use NodeByte::*;
        use SimpleType::*;

        let rc_state = create_simple_state(2, 0, 0).unwrap();
        let results = get_iterator(&rc_state, Boolean, 1);
        assert!(
            results.is_ok(),
            "get_iterator(_, Boolean, 1) should succeed"
        );

        let results = results.unwrap().collect::<Vec<_>>();

        // Should include Not applied to variables
        let v0 = WideMetavariable::try_from_type_and_index(Boolean, 0).unwrap();
        let v1 = WideMetavariable::try_from_type_and_index(Boolean, 1).unwrap();

        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v0)])),
            "Should contain [Not, V0]"
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v1)])),
            "Should contain [Not, V1]"
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(
                Not,
                vec![EnumTerm::NodeOrLeaf(False, vec![])]
            )),
            "Should contain [Not, False]"
        );

        // Should include Implies with all combinations
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(
                Implies,
                vec![EnumTerm::Leaf(v0), EnumTerm::Leaf(v0)]
            )),
            "Should contain [Implies, V0, V0]"
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(
                Implies,
                vec![EnumTerm::Leaf(v0), EnumTerm::Leaf(v1)]
            )),
            "Should contain [Implies, V0, V1]"
        );
        assert!(
            results.contains(&EnumTerm::NodeOrLeaf(
                Implies,
                vec![EnumTerm::Leaf(v1), EnumTerm::Leaf(v0)]
            )),
            "Should contain [Implies, V1, V0]"
        );

        // All results should be Boolean
        assert!(
            results.iter().all(|x| matches!(x.get_type(), Ok(Boolean))),
            "All results should be Boolean type"
        );
    }

    #[test]
    fn get_iterator_depth1_cartesian_product() {
        use NodeByte::*;
        use SimpleType::*;

        // 2 Boolean vars, so depth 0 has 2 vars + 2 nodes = 4 terms
        let rc_state = create_simple_state(2, 0, 0).unwrap();
        let results = get_iterator(&rc_state, Boolean, 1)
            .unwrap()
            .collect::<Vec<_>>();

        // For Implies (arity 2), we should get 4*4 = 16 combinations
        let implies_count = results
            .iter()
            .filter(|term| matches!(term, EnumTerm::NodeOrLeaf(Implies, _)))
            .count();

        assert_eq!(
            implies_count, 16,
            "Should have 16 Implies combinations (4 choices × 4 choices)"
        );

        // For Not (arity 1), we should get 4 combinations
        let not_count = results
            .iter()
            .filter(|term| matches!(term, EnumTerm::NodeOrLeaf(Not, _)))
            .count();

        assert_eq!(not_count, 4, "Should have 4 Not combinations (4 choices)");
    }

    #[test]
    fn get_iterator_depth2_boolean() {
        use NodeByte::*;
        use SimpleType::*;

        let rc_state = create_simple_state(2, 0, 0).unwrap();
        let results = get_iterator(&rc_state, Boolean, 2);
        assert!(
            results.is_ok(),
            "get_iterator(_, Boolean, 2) should succeed"
        );

        let results = results.unwrap().collect::<Vec<_>>();

        assert!(
            !results.is_empty(),
            "Depth 2 should produce some results, got {} results",
            results.len()
        );

        // Should include nested terms like [Not, [Not, V0]]
        let v0 = WideMetavariable::try_from_type_and_index(Boolean, 0).unwrap();
        let not_v0 = EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v0)]);
        let not_not_v0 = EnumTerm::NodeOrLeaf(Not, vec![not_v0.clone()]);

        assert!(
            results.contains(&not_not_v0),
            "Should contain [Not, [Not, V0]]"
        );

        // Should include nested implies like [Implies, V0, [Not, V1]]
        let v1 = WideMetavariable::try_from_type_and_index(Boolean, 1).unwrap();
        let not_v1 = EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v1)]);
        let implies_v0_not_v1 =
            EnumTerm::NodeOrLeaf(Implies, vec![EnumTerm::Leaf(v0), not_v1.clone()]);

        assert!(
            results.contains(&implies_v0_not_v1),
            "Should contain [Implies, V0, [Not, V1]]"
        );

        // All results should be Boolean
        assert!(
            results.iter().all(|x| matches!(x.get_type(), Ok(Boolean))),
            "All results should be Boolean type"
        );
    }

    #[test]
    fn get_iterator_depth2_nested_depth_combinations() {
        use NodeByte::*;
        use SimpleType::*;

        let rc_state = create_simple_state(1, 0, 0).unwrap();
        let results = get_iterator(&rc_state, Boolean, 2)
            .unwrap()
            .collect::<Vec<_>>();

        let v0 = WideMetavariable::try_from_type_and_index(Boolean, 0).unwrap();

        // For Implies at depth 2, depth combinations are [0,1], [1,0], [1,1]
        // [0,1]: first argument from depth 0, second from depth 1
        let implies_v0_not_v0 = EnumTerm::NodeOrLeaf(
            Implies,
            vec![
                EnumTerm::Leaf(v0),
                EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v0)]),
            ],
        );
        assert!(
            results.contains(&implies_v0_not_v0),
            "Should contain [Implies, V0, [Not, V0]] (depth combo [0,1])"
        );

        // [1,0]: first argument from depth 1, second from depth 0
        let implies_not_v0_v0 = EnumTerm::NodeOrLeaf(
            Implies,
            vec![
                EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v0)]),
                EnumTerm::Leaf(v0),
            ],
        );
        assert!(
            results.contains(&implies_not_v0_v0),
            "Should contain [Implies, [Not, V0], V0] (depth combo [1,0])"
        );

        // [1,1]: both argument from depth 1
        let implies_not_v0_not_false = EnumTerm::NodeOrLeaf(
            Implies,
            vec![
                EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::Leaf(v0)]),
                EnumTerm::NodeOrLeaf(Not, vec![EnumTerm::NodeOrLeaf(False, vec![])]),
            ],
        );
        assert!(
            results.contains(&implies_not_v0_not_false),
            "Should contain [Implies, [Not, V0], [Not, False]] (depth combo [1,1])"
        );
    }

    #[test]
    fn get_iterator_type_filtering() {
        use SimpleType::*;

        // Create state with all three types
        let rc_state = create_simple_state(2, 2, 2).unwrap();

        // Boolean depth 0 should only have Boolean terms
        let bool_results = get_iterator(&rc_state, Boolean, 0)
            .unwrap()
            .collect::<Vec<_>>();
        assert!(
            bool_results
                .iter()
                .all(|x| matches!(x.get_type(), Ok(Boolean))),
            "Boolean iterator should only produce Boolean terms"
        );
        assert!(
            !bool_results.is_empty(),
            "Boolean iterator should produce some terms"
        );

        // Setvar depth 0 should only have Setvar terms
        let setvar_results = get_iterator(&rc_state, Setvar, 0)
            .unwrap()
            .collect::<Vec<_>>();
        assert!(
            setvar_results
                .iter()
                .all(|x| matches!(x.get_type(), Ok(Setvar))),
            "Setvar iterator should only produce Setvar terms"
        );
        assert_eq!(
            setvar_results.len(),
            2,
            "Should have exactly 2 Setvar variables"
        );

        // Class depth 0 should only have Class terms
        let class_results = get_iterator(&rc_state, Class, 0)
            .unwrap()
            .collect::<Vec<_>>();
        assert!(
            class_results
                .iter()
                .all(|x| matches!(x.get_type(), Ok(Class))),
            "Class iterator should only produce Class terms"
        );
    }

    #[test]
    fn get_iterator_caching() {
        use SimpleType::*;

        let rc_state = create_simple_state(2, 0, 0).unwrap();

        // First call creates and caches the iterator
        let iter1 = get_iterator(&rc_state, Boolean, 1).unwrap();
        let count1 = iter1.count();

        // Second call should get a fresh clone from cache
        let iter2 = get_iterator(&rc_state, Boolean, 1).unwrap();
        let count2 = iter2.count();

        assert_eq!(
            count1, count2,
            "Cached iterator clone should produce same number of results"
        );
        assert!(count1 > 0, "Should produce some results");
    }
}
