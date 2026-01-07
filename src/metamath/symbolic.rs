//! Integration with main crate traits.
//!
//! This module provides implementations of the traits Type, Metavariable, Node
//! backed by a Metamath database. This enables using Metamath theorems and axioms with
//! the crate's unification and proof search capabilities.
//!
//! # Architecture
//!
//! - **`DbType`**: Maps Metamath type codes (e.g., `"wff"`, `"setvar"`, `"class"`) to the Type trait
//! - **`DbMetavariable`**: Maps Metamath variables to the Metavariable trait
//! - **`DbNode`**: Maps Metamath syntax axioms to the Node trait
//!
//! Each type holds an `Arc<MetamathDatabase>` reference to access type mappings, variable
//! lists, and syntax axiom definitions.

use crate::bool_eval::BooleanSimpleOp;
use crate::metamath::{Label, MetamathDatabase, TypeMapping};
use crate::{
    EnumTerm, Metavariable, MetavariableFactory, MguError, Node, Type, TypeCore, TypeFactory,
};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Term type backed by Metamath database.
///
/// Uses `EnumTerm` parameterized with database-backed types.
/// The `Arc<MetamathDatabase>` references are held within `DbType`,
/// `DbMetavariable`, and `DbNode`, avoiding the need for a wrapper type.
pub type DbTerm = EnumTerm<DbType, DbMetavariable, DbNode>;

impl DbTerm {
    /// Convert this term to a symbol sequence for comparison with Metamath statements.
    ///
    /// Recursively traverses the term tree and outputs the corresponding sequence of
    /// Metamath symbols (constants and variables).
    ///
    /// # Algorithm
    ///
    /// - For a `Leaf(variable)`: Returns the variable's symbol
    /// - For a `NodeOrLeaf(node, children)`:
    ///   - Looks up the syntax axiom by node label
    ///   - Gets the axiom's statement pattern (skipping type code)
    ///   - Substitutes variables in pattern with children's symbol sequences
    ///   - Returns the resulting symbol sequence
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - A syntax axiom is not found for a node
    /// - A variable index is out of bounds
    /// - Recursion fails on a child term
    ///
    /// # Example
    ///
    /// For the term representing `( t + 0 )` constructed from axiom `tpl` with type `term`:
    /// ```text
    /// NodeOrLeaf(tpl, [Leaf(t), Leaf(0)])
    ///   -> ["term", "(", "t", "+", "0", ")"]
    /// ```
    pub fn to_symbol_sequence(&self) -> Result<Vec<Arc<str>>, MguError> {
        match self {
            EnumTerm::Leaf(var) => {
                // Look up the variable's symbol from the database
                let vars = var.database.variables_of_type(&var.key.type_code);
                let symbol = vars.get(var.key.index).ok_or_else(|| {
                    MguError::ArgumentError(format!(
                        "Variable index {} out of bounds for type {} (has {} variables)",
                        var.key.index,
                        var.key.type_code,
                        vars.len()
                    ))
                })?;
                // Return with type code prefix
                Ok(vec![Arc::clone(&var.key.type_code), Arc::clone(symbol)])
            }
            EnumTerm::NodeOrLeaf(node, children) => {
                // Look up the syntax axiom
                let axiom = node.database.get_axiom(node.label()).ok_or_else(|| {
                    MguError::ArgumentError(format!(
                        "Syntax axiom '{}' not found in database",
                        node.label().as_ref()
                    ))
                })?;

                // Get the axiom's statement (pattern)
                let statement = &axiom.core.statement;

                // The first symbol is the type code, skip it
                if statement.is_empty() {
                    return Err(MguError::ArgumentError(
                        "Syntax axiom has empty statement".to_string(),
                    ));
                }

                // Extract type code and pattern
                let type_code = &statement[0];
                let pattern = &statement[1..];

                // Get syntax info to know which symbols are variables
                let syntax_info = axiom.syntax_info.as_ref().ok_or_else(|| {
                    MguError::ArgumentError(format!(
                        "Axiom '{}' is not a syntax axiom",
                        node.label().as_ref()
                    ))
                })?;

                // Convert children to symbol sequences
                let child_sequences: Vec<Vec<Arc<str>>> = children
                    .iter()
                    .map(|child| child.to_symbol_sequence())
                    .collect::<Result<_, _>>()?;

                // Build output by substituting variables with child sequences
                // Start with type code prefix
                let mut result = vec![Arc::clone(type_code)];
                let mut child_index = 0;

                for symbol in pattern {
                    // Check if this symbol is a variable
                    if let Some(var_pos) =
                        syntax_info.distinct_vars.iter().position(|v| v == symbol)
                    {
                        // This is a variable - substitute with corresponding child
                        if child_index >= child_sequences.len() {
                            return Err(MguError::ArgumentError(format!(
                                "Not enough children for axiom '{}': expected {}, got {}",
                                node.label().as_ref(),
                                syntax_info.distinct_vars.len(),
                                children.len()
                            )));
                        }
                        // Skip the type prefix from child sequence (first element)
                        let child_content = if child_sequences[var_pos].len() > 1 {
                            &child_sequences[var_pos][1..]
                        } else {
                            &child_sequences[var_pos][..]
                        };
                        result.extend_from_slice(child_content);
                        child_index += 1;
                    } else {
                        // This is a constant - output as-is
                        result.push(Arc::clone(symbol));
                    }
                }

                Ok(result)
            }
        }
    }
}

/// Factory for constructing [`DbType`] instances from a Metamath database.
///
/// Unlike [`SimpleTypeFactory`](crate::SimpleTypeFactory), `DbTypeFactory` requires
/// database context to construct types, as type codes are database-specific.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::metamath::{DbTypeFactory, MetamathDatabase, TypeMapping};
/// use symbolic_mgu::TypeFactory;
/// use std::sync::Arc;
///
/// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
/// let type_factory = DbTypeFactory::new(Arc::clone(&db));
///
/// // Get Boolean type (wff in set.mm)
/// let wff_type = type_factory.try_boolean().unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct DbTypeFactory {
    /// Reference to the Metamath database for type code lookups.
    database: Arc<MetamathDatabase>,
}

impl DbTypeFactory {
    /// Create a new `DbTypeFactory` with the given database.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbTypeFactory, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let type_factory = DbTypeFactory::new(db);
    /// ```
    #[must_use]
    pub fn new(database: Arc<MetamathDatabase>) -> Self {
        Self { database }
    }
}

impl TypeFactory for DbTypeFactory {
    type Type = DbType;

    fn try_boolean(&self) -> Result<DbType, MguError> {
        let type_code = self
            .database
            .type_mapping()
            .get_boolean_type()
            .clone()
            .ok_or(MguError::TypeCapabilityUnsupported {
                capability: "Boolean",
            })?;
        Ok(DbType::new(type_code, Arc::clone(&self.database)))
    }

    fn try_setvar(&self) -> Result<DbType, MguError> {
        let type_code = self
            .database
            .type_mapping()
            .get_setvar_type()
            .clone()
            .ok_or(MguError::TypeCapabilityUnsupported {
                capability: "Setvar",
            })?;
        Ok(DbType::new(type_code, Arc::clone(&self.database)))
    }

    fn try_class(&self) -> Result<DbType, MguError> {
        let type_code = self
            .database
            .type_mapping()
            .get_class_type()
            .clone()
            .ok_or(MguError::TypeCapabilityUnsupported {
                capability: "Class",
            })?;
        Ok(DbType::new(type_code, Arc::clone(&self.database)))
    }
}

/// A Type implementation backed by a Metamath database.
///
/// `DbType` represents a Metamath type code (e.g., `"wff"`, `"setvar"`, `"class"`)
/// with access to the database's `TypeMapping` for type queries.
///
/// # Constructing `DbType`
///
/// Unlike [`SimpleType`](crate::SimpleType), `DbType` requires a database context.
/// The [`Type`] trait methods `try_boolean()`, `try_setvar()`, and `try_class()`
/// will panic if called. Instead, use [`DbType::new()`] with a database reference:
///
/// ```
/// # use symbolic_mgu::metamath::{DbType, MetamathDatabase, TypeMapping};
/// # use std::sync::Arc;
/// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
/// let wff_type = DbType::new(Arc::from("wff"), db);
/// ```
///
/// # Memory Layout
///
/// Uses `Arc<str>` for the type code and `Arc<MetamathDatabase>` for database
/// access, making cloning cheap (just reference count increments).
#[derive(Debug, Clone)]
pub struct DbType {
    /// The Metamath type code (e.g., `"wff"`, `"setvar"`, `"class"`).
    type_code: Arc<str>,
    /// Reference to the database for type mapping queries.
    database: Arc<MetamathDatabase>,
}

impl DbType {
    /// Create a new `DbType` from a type code and database reference.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbType, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let wff_type = DbType::new(Arc::from("wff"), db);
    /// ```
    pub fn new(type_code: Arc<str>, database: Arc<MetamathDatabase>) -> Self {
        Self {
            type_code,
            database,
        }
    }

    /// Get the Metamath type code.
    pub fn type_code(&self) -> &str {
        &self.type_code
    }

    /// Get the database reference.
    pub fn database(&self) -> &Arc<MetamathDatabase> {
        &self.database
    }

    /// Get the type mapping from the database.
    fn type_mapping(&self) -> &TypeMapping {
        self.database.type_mapping()
    }
}

// Implement PartialEq manually - compare type codes only
// (two types with same code from different databases are considered equal)
impl PartialEq for DbType {
    fn eq(&self, other: &Self) -> bool {
        self.type_code == other.type_code
    }
}

impl Eq for DbType {}

// Implement Hash manually - hash type code only
impl Hash for DbType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.type_code.hash(state);
    }
}

// Implement PartialOrd/Ord for canonicalization
impl PartialOrd for DbType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DbType {
    fn cmp(&self, other: &Self) -> Ordering {
        self.type_code.cmp(&other.type_code)
    }
}

impl fmt::Display for DbType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.type_code)
    }
}

impl TypeCore for DbType {
    fn is_boolean(&self) -> bool {
        self.type_mapping().is_boolean(&self.type_code)
    }

    fn is_setvar(&self) -> bool {
        self.type_mapping().is_setvar(&self.type_code)
    }

    fn is_class(&self) -> bool {
        self.type_mapping().is_class(&self.type_code)
    }
}

impl Type for DbType {
    fn is_subtype_of(&self, other: &Self) -> bool {
        // A type is only a sub-type of itself.
        // Type conversions (e.g., `setvar` to class) must go through explicit syntax axioms
        // like `"cv"` in the proof, not through implicit sub-typing.
        self == other
    }
}

/// A Metavariable implementation backed by a Metamath database.
///
/// `DbMetavariable` represents a variable with its type and index within that type.
/// Variables are identified by a `(type_code, index)` pair, where the index corresponds
/// to the declaration order of variables of that type.
///
/// # Memory Layout
///
/// Uses `Arc<str>` for the type code and `Arc<MetamathDatabase>` for database
/// access, making cloning cheap (just reference count increments).
///
/// Immutable key for `DbMetavariable` that can safely be used in `HashMap` and `HashSet`.
///
/// This key contains only the immutable identity of a metavariable (`type_code` and `index`)
/// without the database reference, making it suitable for use as a hash key.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DbMetavariableKey {
    /// The Metamath type code (e.g., `"wff"`, `"setvar"`, `"class"`)
    pub type_code: Arc<str>,
    /// Index within variables of this type (0-based, in declaration order)
    pub index: usize,
}

impl DbMetavariableKey {
    /// Create a new key from type code and index.
    #[must_use]
    pub fn new(type_code: Arc<str>, index: usize) -> Self {
        Self { type_code, index }
    }
}

/// A Metavariable implementation backed by a Metamath database.
///
/// `DbMetavariable` represents a variable with its type and index within that type.
/// Variables are identified by a `(type_code, index)` pair, where the index corresponds
/// to the declaration order of variables of that type.
///
/// # Memory Layout
///
/// Uses `Arc<str>` for the type code and `Arc<MetamathDatabase>` for database
/// access, making cloning cheap (just reference count increments).
///
/// # `HashMap` and `HashSet` Usage
///
/// This type can be used directly in `HashMap` and `HashSet`, as its `Hash` and `Eq`
/// implementations are based only on the immutable `DbMetavariableKey`. For better
/// performance when frequently used as a key, consider using `key()` to get a reference
/// to the lightweight `DbMetavariableKey` instead.
#[derive(Debug, Clone)]
pub struct DbMetavariable {
    /// Immutable identity (type code and index)
    key: DbMetavariableKey,
    /// Reference to the database for variable lookups
    database: Arc<MetamathDatabase>,
}

impl DbMetavariable {
    /// Create a new `DbMetavariable` from a type code, index, and database reference.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbMetavariable, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let mut db = MetamathDatabase::new(TypeMapping::set_mm());
    /// // Assume variables have been registered
    /// let db = Arc::new(db);
    /// // let var = DbMetavariable::new(Arc::from("wff"), 0, db);
    /// ```
    pub fn new(type_code: Arc<str>, index: usize, database: Arc<MetamathDatabase>) -> Self {
        Self {
            key: DbMetavariableKey::new(type_code, index),
            database,
        }
    }

    /// Get the immutable key for use in `HashMap`/`HashSet`.
    ///
    /// This key contains only the identity (`type_code` and `index`) without the database
    /// reference, making it safe to use as a hash key despite the interior mutability of
    /// the database's `RwLock` fields.
    #[must_use]
    pub fn key(&self) -> &DbMetavariableKey {
        &self.key
    }

    /// Get the type code.
    pub fn type_code(&self) -> &str {
        &self.key.type_code
    }

    /// Get the index within variables of this type.
    pub fn index(&self) -> usize {
        self.key.index
    }

    /// Get the database reference.
    pub fn database(&self) -> &Arc<MetamathDatabase> {
        &self.database
    }

    /// Get the variable name from the database.
    ///
    /// Returns `None` if the index is out of bounds.
    fn variable_name(&self) -> Option<Arc<str>> {
        let vars = self.database.variables_of_type(&self.key.type_code);
        vars.get(self.key.index).cloned()
    }
}

// PartialEq compares keys only
impl PartialEq for DbMetavariable {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for DbMetavariable {}

// Hash uses key only
impl Hash for DbMetavariable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
    }
}

// Ord for canonicalization (delegates to key)
impl PartialOrd for DbMetavariable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DbMetavariable {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl fmt::Display for DbMetavariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Display the variable name from the database if available
        if let Some(name) = self.variable_name() {
            write!(f, "{}", name)
        } else {
            // Fallback if index is out of bounds
            write!(f, "{}#{}", self.key.type_code, self.key.index)
        }
    }
}

impl Metavariable for DbMetavariable {
    type Type = DbType;

    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError> {
        let db_type = DbType::new(self.key.type_code.clone(), self.database.clone());
        Ok((db_type, self.key.index))
    }

    fn max_index_by_type(_typ: Self::Type) -> usize {
        // For `DbMetavariable` backed by a database, we have a finite number of variables
        // The maximum index is the count of variables of that type
        // However, this method is static, so we can't access the database here
        // We'll return usize::MAX to indicate unlimited (variables can be added dynamically)
        usize::MAX
    }

    fn try_from_type_and_index(my_type: Self::Type, my_index: usize) -> Result<Self, MguError> {
        // Verify that the index is within bounds
        let vars = my_type.database().variables_of_type(my_type.type_code());
        if my_index >= vars.len() {
            return Err(MguError::from_index_and_len(my_index, vars.len()));
        }

        Ok(Self::new(
            my_type.type_code.clone(),
            my_index,
            my_type.database.clone(),
        ))
    }
}

/// A `MetavariableFactory` implementation backed by a Metamath database.
///
/// `DbMetavariableFactory` creates `DbMetavariable` instances from a database,
/// supporting variable lookup by name or by type and index.
#[derive(Debug, Clone)]
pub struct DbMetavariableFactory {
    /// Type factory for constructing type instances.
    type_factory: DbTypeFactory,
    /// Reference to the database for variable lookups
    database: Arc<MetamathDatabase>,
}

impl DbMetavariableFactory {
    /// Create a new `DbMetavariableFactory` from a type factory.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbTypeFactory, DbMetavariableFactory, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let type_factory = DbTypeFactory::new(Arc::clone(&db));
    /// let var_factory = DbMetavariableFactory::new(type_factory, db);
    /// ```
    pub fn new(type_factory: DbTypeFactory, database: Arc<MetamathDatabase>) -> Self {
        Self {
            type_factory,
            database,
        }
    }

    /// Get the database reference.
    pub fn database(&self) -> &Arc<MetamathDatabase> {
        &self.database
    }

    /// Create a `DbMetavariable` from a `DbMetavariableKey`.
    ///
    /// This allows recovering the full `DbMetavariable` (with database reference) from
    /// an immutable key that was used in a `HashMap` or `HashSet`.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbMetavariableFactory, DbTypeFactory, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let type_factory = DbTypeFactory::new(Arc::clone(&db));
    /// let var_factory = DbMetavariableFactory::new(type_factory, Arc::clone(&db));
    ///
    /// // Get a metavariable and its key
    /// // let var = ...;
    /// // let key = var.key().clone();
    /// // Later, recover the full metavariable from the key
    /// // let recovered = var_factory.from_key(&key);
    /// ```
    #[must_use]
    pub fn from_key(&self, key: &DbMetavariableKey) -> DbMetavariable {
        DbMetavariable::new(
            Arc::clone(&key.type_code),
            key.index,
            Arc::clone(&self.database),
        )
    }
}

impl MetavariableFactory<DbTypeFactory> for DbMetavariableFactory {
    type Metavariable = DbMetavariable;
    type MetavariableType = DbType;
    type MetavariableIterator<'a> = DbMetavariableIterator<'a>;

    fn type_factory(&self) -> &DbTypeFactory {
        &self.type_factory
    }

    fn create_by_name(&self, name: &str) -> Result<Self::Metavariable, MguError> {
        // Look up the variable in the database
        let (type_code, index) = self
            .database
            .variable_type_and_index(name)
            .ok_or_else(|| MguError::from_type_and_var_strings("unknown", name))?;

        Ok(DbMetavariable::new(
            type_code.clone(),
            index,
            self.database.clone(),
        ))
    }

    fn create_by_type_and_index(
        &self,
        the_type: &Self::MetavariableType,
        index: usize,
    ) -> Result<Self::Metavariable, MguError> {
        DbMetavariable::try_from_type_and_index(the_type.clone(), index)
    }

    fn list_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> Self::MetavariableIterator<'_> {
        DbMetavariableIterator::new(the_type.clone(), self.database.clone())
    }

    fn count_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> (usize, Option<usize>) {
        let count = self.database.variables_of_type(the_type.type_code()).len();
        (count, Some(count))
    }
}

/// Iterator over `DbMetavariable`s of a given type.
pub struct DbMetavariableIterator<'a> {
    /// The type code of variables being iterated
    type_code: Arc<str>,
    /// Reference to the database for variable lookups
    database: Arc<MetamathDatabase>,
    /// Current index in the iteration
    index: usize,
    /// Phantom data to tie the lifetime to the iterator
    _phantom: std::marker::PhantomData<&'a ()>,
}

impl DbMetavariableIterator<'_> {
    /// Create a new iterator for variables of a given type.
    fn new(db_type: DbType, database: Arc<MetamathDatabase>) -> Self {
        Self {
            type_code: db_type.type_code,
            database,
            index: 0,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl Iterator for DbMetavariableIterator<'_> {
    type Item = DbMetavariable;

    fn next(&mut self) -> Option<Self::Item> {
        let vars = self.database.variables_of_type(&self.type_code);
        if self.index < vars.len() {
            let var =
                DbMetavariable::new(self.type_code.clone(), self.index, self.database.clone());
            self.index += 1;
            Some(var)
        } else {
            None
        }
    }
}

/// A Node implementation backed by a Metamath database.
///
/// `DbNode` represents a syntax axiom (operation/constructor) identified by its label.
/// For example, the implication operator might have label `"wi"` corresponding to
/// the syntax axiom `$a wff ( ph -> ps )`.
///
/// # Note
///
/// Full arity and slot type information requires parsing syntax axioms, which is
/// deferred to future work. For now, these methods will return errors or placeholder values.
#[derive(Debug, Clone)]
pub struct DbNode {
    /// Label of the syntax axiom (e.g., `"wi"` for implication)
    label: Label,
    /// Reference to the database for syntax axiom lookups
    database: Arc<MetamathDatabase>,
}

impl DbNode {
    /// Create a new `DbNode` from a label and database reference.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::{DbNode, Label, MetamathDatabase, TypeMapping};
    /// use std::sync::Arc;
    ///
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// let label = Label::new("wi").unwrap();
    /// let node = DbNode::new(label, db);
    /// ```
    pub fn new(label: Label, database: Arc<MetamathDatabase>) -> Self {
        Self { label, database }
    }

    /// Get the label of this node.
    pub fn label(&self) -> &Label {
        &self.label
    }

    /// Get the database reference.
    pub fn database(&self) -> &Arc<MetamathDatabase> {
        &self.database
    }
}

// PartialEq compares labels only
impl PartialEq for DbNode {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}

impl Eq for DbNode {}

// Hash uses label only
impl Hash for DbNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.label.hash(state);
    }
}

// Ord for canonicalization (order by label)
impl PartialOrd for DbNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DbNode {
    fn cmp(&self, other: &Self) -> Ordering {
        self.label.cmp(&other.label)
    }
}

impl fmt::Display for DbNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.label)
    }
}

impl Node for DbNode {
    type Type = DbType;

    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError> {
        // Look up the syntax axiom for this node
        let axiom = self.database.get_axiom(&self.label).ok_or_else(|| {
            let msg = format!("Axiom '{}' not found", self.label);
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        // Check if it's a syntax axiom
        let _syntax_info = axiom.syntax_info.as_ref().ok_or_else(|| {
            let msg = format!(
                "Axiom '{}' is not a syntax axiom (type code is '{}')",
                self.label, axiom.type_code
            );
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        // For Node trait, return (type, 0) - nodes don't have indices like metavariables
        let node_type = DbType::new(axiom.type_code.clone(), Arc::clone(&self.database));
        Ok((node_type, 0))
    }

    fn get_arity(&self) -> Result<usize, MguError> {
        // Look up the syntax axiom for this node
        let axiom = self.database.get_axiom(&self.label).ok_or_else(|| {
            let msg = format!("Axiom '{}' not found", self.label);
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        // Check if it's a syntax axiom
        let syntax_info = axiom.syntax_info.as_ref().ok_or_else(|| {
            let msg = format!(
                "Axiom '{}' is not a syntax axiom (type code is '{}')",
                self.label, axiom.type_code
            );
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        Ok(syntax_info.arity())
    }

    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError> {
        // Look up the syntax axiom for this node
        let axiom = self.database.get_axiom(&self.label).ok_or_else(|| {
            let msg = format!("Axiom '{}' not found", self.label);
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        // Check if it's a syntax axiom
        let syntax_info = axiom.syntax_info.as_ref().ok_or_else(|| {
            let msg = format!(
                "Axiom '{}' is not a syntax axiom (type code is '{}')",
                self.label, axiom.type_code
            );
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        // Check bounds
        if index >= syntax_info.distinct_vars.len() {
            return Err(MguError::from_index_and_len(
                index,
                syntax_info.distinct_vars.len(),
            ));
        }

        // Get the variable at this slot
        let var = &syntax_info.distinct_vars[index];

        // Look up its type
        let type_code = self.database.variable_type(var).ok_or_else(|| {
            let msg = format!("Variable '{}' has no type binding", var);
            MguError::from_type_and_var_strings("DbNode", msg.as_str())
        })?;

        Ok(DbType::new(type_code, Arc::clone(&self.database)))
    }

    fn to_boolean_op(&self) -> Option<BooleanSimpleOp> {
        self.database.get_boolean_op(self.label.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::TypeMapping;
    use crate::{EnumTerm, Term};

    #[test]
    fn dbtype_creation() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wff = DbType::new(Arc::from("wff"), Arc::clone(&db));

        assert_eq!(wff.type_code(), "wff");
        assert!(wff.is_boolean());
        assert!(!wff.is_setvar());
        assert!(!wff.is_class());
    }

    #[test]
    fn dbtype_equality() {
        let db1 = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let db2 = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        let wff1 = DbType::new(Arc::from("wff"), Arc::clone(&db1));
        let wff2 = DbType::new(Arc::from("wff"), Arc::clone(&db2));
        let setvar = DbType::new(Arc::from("setvar"), Arc::clone(&db1));

        // Same type code = equal (even from different databases)
        assert_eq!(wff1, wff2);
        assert_ne!(wff1, setvar);
    }

    #[test]
    fn dbtype_subtyping() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wff = DbType::new(Arc::from("wff"), Arc::clone(&db));
        let setvar = DbType::new(Arc::from("setvar"), Arc::clone(&db));
        let class = DbType::new(Arc::from("class"), Arc::clone(&db));

        // Each type is only a sub-type of itself
        // Type conversions must be explicit through syntax axioms like `"cv"`
        assert!(wff.is_subtype_of(&wff));
        assert!(setvar.is_subtype_of(&setvar));
        assert!(class.is_subtype_of(&class));

        // No implicit sub-typing between different types
        assert!(!setvar.is_subtype_of(&class));
        assert!(!class.is_subtype_of(&setvar));
        assert!(!wff.is_subtype_of(&setvar));
        assert!(!wff.is_subtype_of(&class));
    }

    #[test]
    fn dbtype_ordering() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let class = DbType::new(Arc::from("class"), Arc::clone(&db));
        let setvar = DbType::new(Arc::from("setvar"), Arc::clone(&db));
        let wff = DbType::new(Arc::from("wff"), Arc::clone(&db));

        // Alphabetical ordering by type code
        assert!(class < setvar);
        assert!(setvar < wff);
        assert!(class < wff);
    }

    #[test]
    fn dbmetavariable_creation() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Register some variables
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 3)
            .unwrap();

        let db = Arc::new(db);

        // Create metavariables
        let ph = DbMetavariable::new(Arc::from("wff"), 0, Arc::clone(&db));
        let ps = DbMetavariable::new(Arc::from("wff"), 1, Arc::clone(&db));
        let x = DbMetavariable::new(Arc::from("setvar"), 0, Arc::clone(&db));

        assert_eq!(ph.type_code(), "wff");
        assert_eq!(ph.index(), 0);
        assert_eq!(ph.to_string(), "ph");

        assert_eq!(ps.type_code(), "wff");
        assert_eq!(ps.index(), 1);
        assert_eq!(ps.to_string(), "ps");

        assert_eq!(x.type_code(), "setvar");
        assert_eq!(x.index(), 0);
        assert_eq!(x.to_string(), "x");
    }

    #[test]
    fn dbmetavariable_equality() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        let db = Arc::new(db);

        let ph1 = DbMetavariable::new(Arc::from("wff"), 0, Arc::clone(&db));
        let ph2 = DbMetavariable::new(Arc::from("wff"), 0, Arc::clone(&db));
        let ps = DbMetavariable::new(Arc::from("wff"), 1, Arc::clone(&db));

        // Same (type, index) = equal
        assert_eq!(ph1, ph2);
        assert_ne!(ph1, ps);
    }

    #[test]
    fn dbmetavariable_ordering() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 3)
            .unwrap();
        let db = Arc::new(db);

        let ph = DbMetavariable::new(Arc::from("wff"), 0, Arc::clone(&db));
        let ps = DbMetavariable::new(Arc::from("wff"), 1, Arc::clone(&db));
        let x = DbMetavariable::new(Arc::from("setvar"), 0, Arc::clone(&db));

        // Order by `type_code` first, then `index`
        assert!(x < ph); // `"setvar"` < `"wff"`
        assert!(x < ps);
        assert!(ph < ps); // same type, index 0 < 1
    }

    #[test]
    fn dbmetavariable_get_type_and_index() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        let db = Arc::new(db);

        let ph = DbMetavariable::new(Arc::from("wff"), 0, Arc::clone(&db));

        let (typ, index) = ph.get_type_and_index().unwrap();
        assert_eq!(typ.type_code(), "wff");
        assert!(typ.is_boolean());
        assert_eq!(index, 0);
    }

    #[test]
    fn dbmetavariable_try_from_type_and_index() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        let db = Arc::new(db);

        let wff_type = DbType::new(Arc::from("wff"), Arc::clone(&db));

        // Valid index
        let ph = DbMetavariable::try_from_type_and_index(wff_type.clone(), 0).unwrap();
        assert_eq!(ph.to_string(), "ph");

        let ps = DbMetavariable::try_from_type_and_index(wff_type.clone(), 1).unwrap();
        assert_eq!(ps.to_string(), "ps");

        // Out of bounds index
        let result = DbMetavariable::try_from_type_and_index(wff_type, 2);
        assert!(result.is_err());
    }

    #[test]
    fn dbmetavariable_factory_creation() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 3)
            .unwrap();
        let db = Arc::new(db);

        let factory = DbMetavariableFactory::new(DbTypeFactory::new(db.clone()), db.clone());

        // Create by name
        let ph = factory.create_by_name("ph").unwrap();
        assert_eq!(ph.to_string(), "ph");
        assert_eq!(ph.type_code(), "wff");
        assert_eq!(ph.index(), 0);

        let x = factory.create_by_name("x").unwrap();
        assert_eq!(x.to_string(), "x");
        assert_eq!(x.type_code(), "setvar");
        assert_eq!(x.index(), 0);

        // Unknown variable
        let result = factory.create_by_name("unknown");
        assert!(result.is_err());
    }

    #[test]
    fn dbmetavariable_factory_create_by_type_and_index() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        let db = Arc::new(db);

        let factory = DbMetavariableFactory::new(DbTypeFactory::new(db.clone()), Arc::clone(&db));
        let wff_type = DbType::new(Arc::from("wff"), Arc::clone(&db));

        let ph = factory.create_by_type_and_index(&wff_type, 0).unwrap();
        assert_eq!(ph.to_string(), "ph");

        let ps = factory.create_by_type_and_index(&wff_type, 1).unwrap();
        assert_eq!(ps.to_string(), "ps");
    }

    #[test]
    fn dbmetavariable_factory_list_by_type() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ch"), 3)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 4)
            .unwrap();
        let db = Arc::new(db);

        let factory = DbMetavariableFactory::new(DbTypeFactory::new(db.clone()), Arc::clone(&db));
        let wff_type = DbType::new(Arc::from("wff"), Arc::clone(&db));

        // List all wff variables
        let wff_vars: Vec<_> = factory.list_metavariables_by_type(&wff_type).collect();
        assert_eq!(wff_vars.len(), 3);
        assert_eq!(wff_vars[0].to_string(), "ph");
        assert_eq!(wff_vars[1].to_string(), "ps");
        assert_eq!(wff_vars[2].to_string(), "ch");
    }

    #[test]
    fn dbmetavariable_factory_count_by_type() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 3)
            .unwrap();
        let db = Arc::new(db);

        let factory = DbMetavariableFactory::new(DbTypeFactory::new(db.clone()), Arc::clone(&db));
        let wff_type = DbType::new(Arc::from("wff"), Arc::clone(&db));
        let setvar_type = DbType::new(Arc::from("setvar"), Arc::clone(&db));

        let (min, max) = factory.count_metavariables_by_type(&wff_type);
        assert_eq!(min, 2);
        assert_eq!(max, Some(2));

        let (min, max) = factory.count_metavariables_by_type(&setvar_type);
        assert_eq!(min, 1);
        assert_eq!(max, Some(1));
    }

    #[test]
    fn dbnode_creation() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wi = Label::new("wi").unwrap();
        let wn = Label::new("wn").unwrap();

        let impl_node = DbNode::new(wi.clone(), Arc::clone(&db));
        let not_node = DbNode::new(wn, Arc::clone(&db));

        assert_eq!(impl_node.label(), &wi);
        assert_eq!(impl_node.to_string(), "wi");
        assert_eq!(not_node.to_string(), "wn");
    }

    #[test]
    fn dbnode_equality() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wi1 = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db));
        let wi2 = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db));
        let wn = DbNode::new(Label::new("wn").unwrap(), Arc::clone(&db));

        // Same label = equal
        assert_eq!(wi1, wi2);
        assert_ne!(wi1, wn);
    }

    #[test]
    fn dbnode_ordering() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wa = DbNode::new(Label::new("wa").unwrap(), Arc::clone(&db)); // and
        let wb = DbNode::new(Label::new("wb").unwrap(), Arc::clone(&db)); // biconditional
        let wi = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db)); // implies
        let wn = DbNode::new(Label::new("wn").unwrap(), Arc::clone(&db)); // not
        let wo = DbNode::new(Label::new("wo").unwrap(), Arc::clone(&db)); // or

        // Alphabetical ordering by label
        assert!(wa < wb);
        assert!(wb < wi);
        assert!(wi < wn);
        assert!(wn < wo);
    }

    #[test]
    fn dbnode_to_boolean_op() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        // Currently returns None - will be configurable via registry when syntax axiom parsing is implemented
        let wn = DbNode::new(Label::new("wn").unwrap(), Arc::clone(&db));
        assert_eq!(wn.to_boolean_op(), None);

        let wi = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db));
        assert_eq!(wi.to_boolean_op(), None);
    }

    #[test]
    fn dbnode_unimplemented_methods() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
        let wi = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db));

        // These methods return errors until syntax axiom parsing is implemented
        assert!(wi.get_type_and_index().is_err());
        assert!(wi.get_arity().is_err());
        assert!(wi.get_slot_type(0).is_err());
    }

    /// Integration test verifying `DbType`, `DbMetavariable`, `DbNode` work together with
    /// the `Term` construction.
    #[test]
    fn integration_term_construction() {
        // Create database and register variables with types
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Register variables: ph, ps, ch (`"wff"` type) and x, y (`"setvar"` type)
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ch"), 3)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 4)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("y"), 5)
            .unwrap();

        let db = Arc::new(db);

        // Create factory
        let factory = DbMetavariableFactory::new(DbTypeFactory::new(db.clone()), Arc::clone(&db));

        // Create metavariables by name
        let ph = factory.create_by_name("ph").unwrap();
        let ps = factory.create_by_name("ps").unwrap();
        let ch = factory.create_by_name("ch").unwrap();
        let x = factory.create_by_name("x").unwrap();
        let y = factory.create_by_name("y").unwrap();

        // Verify variable types
        assert_eq!(ph.get_type().unwrap().type_code() as &str, "wff");
        assert_eq!(ps.get_type().unwrap().type_code() as &str, "wff");
        assert_eq!(ch.get_type().unwrap().type_code() as &str, "wff");
        assert_eq!(x.get_type().unwrap().type_code() as &str, "setvar");
        assert_eq!(y.get_type().unwrap().type_code() as &str, "setvar");

        // Create Terms using EnumTerm
        // Simple metavariable term: ph
        let term_ph: EnumTerm<DbType, DbMetavariable, DbNode> = EnumTerm::Leaf(ph.clone());
        assert!(term_ph.is_metavariable());
        assert_eq!(term_ph.get_metavariable(), Some(ph.clone()));
        assert!(term_ph.get_node().is_none());
        assert_eq!(term_ph.get_n_children(), 0);

        // Note: The following node applications would require arity information from
        // syntax axioms, which is not yet implemented. When syntax axiom parsing is
        // added, we can extend this test with:
        //
        // Create node for implication (`"wi"`)
        let wi_node = DbNode::new(Label::new("wi").unwrap(), Arc::clone(&db));

        // Build term: (ph -> ps)
        let term_implies =
            EnumTerm::NodeOrLeaf(wi_node, vec![term_ph.clone(), EnumTerm::Leaf(ps.clone())]);

        assert!(!term_implies.is_metavariable());
        assert_eq!(term_implies.get_n_children(), 2);

        // For now, verify that metavariable factory works correctly
        let wff_type = DbType::new("wff".into(), Arc::clone(&db));
        let (wff_count, wff_max) = factory.count_metavariables_by_type(&wff_type);
        assert_eq!(wff_count, 3); // ph, ps, ch
        assert_eq!(wff_max, Some(3));

        let setvar_type = DbType::new("setvar".into(), Arc::clone(&db));
        let (setvar_count, setvar_max) = factory.count_metavariables_by_type(&setvar_type);
        assert_eq!(setvar_count, 2); // x, y
        assert_eq!(setvar_max, Some(2));

        // Verify metavariable iteration
        let wff_vars: Vec<_> = factory.list_metavariables_by_type(&wff_type).collect();
        assert_eq!(wff_vars.len(), 3);
        assert!(wff_vars.contains(&ph));
        assert!(wff_vars.contains(&ps));
        assert!(wff_vars.contains(&ch));

        // Display formatting
        assert_eq!(format!("{}", term_ph), "ph");
    }
}
