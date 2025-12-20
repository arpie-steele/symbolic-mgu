//! Metamath database structure with scoping support.
//!
//! This module implements the core database structures for parsing and storing
//! Metamath statements, including:
//! - Scoped variables and hypotheses
//! - Global constants, axioms, and theorems
//! - Type mapping configuration for different databases
//! - Comment preservation with metadata
//!
//! # Scoping Rules
//!
//! Metamath has specific scoping rules:
//! - Constants (`$c`) are global, declared only in outermost scope
//! - Variables (`$v`) are scoped but can be re-declared after going inactive
//! - Hypotheses (`$f`, `$e`) are scoped
//! - Distinctness constraints (`$d`) are scoped
//! - Axioms (`$a`) and theorems (`$p`) are global
//!
//! # Example
//!
//! ```no_run
//! use symbolic_mgu::metamath::{MetamathDatabase, TypeMapping};
//!
//! // Create a database configured for `set.mm`
//! let mut db = MetamathDatabase::new(TypeMapping::set_mm());
//!
//! // Parse statements (to be implemented)
//! // db.parse_file("set.mm")?;
//! ```

use crate::metamath::{
    parse_expression, parse_sequence, CommentMetadata, DbMetavariable, DbMetavariableFactory,
    DbNode, DbTerm, DbType, Label, Proof, SyntaxAxiomPattern,
};
use crate::{DistinctnessGraph, MetavariableFactory, MguError, Statement};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock};
use thiserror::Error;

/// Map variable to type code and index.
type VarMap = RwLock<HashMap<Arc<str>, (Arc<str>, usize)>>;

/// Classification of symbols (constant vs variable).
///
/// In Metamath, symbols are declared as either constants (`$c`) or variables (`$v`)
/// before they are used in statements. A symbol cannot be both.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// Constant symbol (declared with `$c`)
    Constant,
    /// Variable symbol (declared with `$v`)
    Variable,
}

/// Errors that can occur during database operations.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum DatabaseError {
    /// A symbol is already in use.
    #[error("Symbol '{symbol}' is already defined at line {previous_line}")]
    SymbolInUse {
        /// The conflicting symbol
        symbol: String,
        /// Line where previously defined
        previous_line: usize,
    },

    /// A label is already in use.
    #[error("Label '{label}' is already in use at line {previous_line}")]
    LabelInUse {
        /// The conflicting label
        label: String,
        /// Line where previously defined
        previous_line: usize,
    },

    /// An illegal symbol was used.
    #[error("Illegal symbol '{symbol}': {reason}")]
    IllegalSymbol {
        /// The illegal symbol
        symbol: String,
        /// Reason why it's illegal
        reason: String,
    },

    /// A symbol was not found.
    #[error("Symbol '{symbol}' is not defined")]
    NoSuchSymbol {
        /// The undefined symbol
        symbol: String,
    },

    /// A constant was not found.
    #[error("Constant '{symbol}' is not defined")]
    NoSuchConstant {
        /// The undefined constant
        symbol: String,
    },

    /// A variable was not found.
    #[error("Variable '{symbol}' is not defined")]
    NoSuchVariable {
        /// The undefined variable
        symbol: String,
    },

    /// A variable is not active in the current scope.
    #[error("Variable '{symbol}' is not active in this scope")]
    InactiveVariable {
        /// The inactive variable
        symbol: String,
    },

    /// Attempted to declare a constant in a non-outermost scope.
    #[error("Constants can only be declared in the outermost scope (line {line})")]
    ConstantInInnerScope {
        /// Line number of the error
        line: usize,
    },

    /// Scope mismatch (e.g., `$}` without `${`).
    #[error("Scope mismatch at line {line}: {message}")]
    ScopeMismatch {
        /// Line number of the error
        line: usize,
        /// Error message
        message: String,
    },

    /// Variable registered with conflicting type.
    #[error("Variable '{symbol}' already registered as type '{existing_type}', cannot re-register as '{new_type}' (line {line})")]
    TypeConflict {
        /// The variable symbol
        symbol: String,
        /// The existing type
        existing_type: String,
        /// The new type attempted
        new_type: String,
        /// Line number of the conflict
        line: usize,
    },

    /// Invalid slot index for syntax axiom.
    #[error("Slot index {slot} out of bounds (arity = {arity})")]
    InvalidSlotIndex {
        /// The requested slot index
        slot: usize,
        /// The arity of the syntax axiom
        arity: usize,
    },

    /// Variable type not found.
    #[error("Variable '{variable}' has no type binding")]
    VariableNotFound {
        /// The variable symbol
        variable: String,
    },

    /// Axiom is not a syntax axiom.
    #[error("Axiom '{label}' is not a syntax axiom (type code is '{type_code}')")]
    NotASyntaxAxiom {
        /// The axiom label
        label: String,
        /// The type code
        type_code: String,
    },

    /// Axiom not found.
    #[error("Axiom '{label}' not found")]
    AxiomNotFound {
        /// The axiom label
        label: String,
    },
}

/// Configuration for mapping Metamath type codes to internal representations.
///
/// Different Metamath databases use different type systems. This struct allows
/// the parser to be configured for different databases.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::metamath::TypeMapping;
///
/// // For `set.mm`
/// let mapping = TypeMapping::set_mm();
///
/// // For `hol.mm`
/// let mapping = TypeMapping::hol_mm();
/// ```
#[derive(Debug, Clone)]
pub struct TypeMapping {
    /// Type codes that represent Boolean/wff types.
    boolean_types: HashSet<Arc<str>>,
    /// Type codes that represent set variables.
    setvar_types: HashSet<Arc<str>>,
    /// Type codes that represent class expressions.
    class_types: HashSet<Arc<str>>,
    /// Type code used for logical assertions (e.g., "|-" in set.mm).
    ///
    /// Statements with this type code are logical axioms/theorems asserting logical truths,
    /// as opposed to syntax axioms that define term constructors.
    assertion_type: Arc<str>,
}

impl TypeMapping {
    /// Standard mapping for `set.mm` and `iset.mm` databases.
    ///
    /// Maps:
    /// - `wff` → Boolean
    /// - `setvar` → set variable
    /// - `class` → class expression
    /// - `|-` → logical assertion
    pub fn set_mm() -> Self {
        let mut boolean_types = HashSet::new();
        boolean_types.insert(Arc::from("wff"));

        let mut setvar_types = HashSet::new();
        setvar_types.insert(Arc::from("setvar"));

        let mut class_types = HashSet::new();
        class_types.insert(Arc::from("class"));

        Self {
            boolean_types,
            setvar_types,
            class_types,
            assertion_type: Arc::from("|-"),
        }
    }

    /// Standard mapping for `hol.mm` database.
    ///
    /// Maps:
    /// - `bool` → Boolean
    /// - `|-` → logical assertion
    pub fn hol_mm() -> Self {
        let mut boolean_types = HashSet::new();
        boolean_types.insert(Arc::from("bool"));

        Self {
            boolean_types,
            setvar_types: HashSet::new(),
            class_types: HashSet::new(),
            assertion_type: Arc::from("|-"),
        }
    }

    /// Check if a type code represents a Boolean/wff type.
    pub fn is_boolean(&self, type_code: &str) -> bool {
        self.boolean_types.contains(type_code)
    }

    /// Check if a type code represents a set variable type.
    pub fn is_setvar(&self, type_code: &str) -> bool {
        self.setvar_types.contains(type_code)
    }

    /// Check if a type code represents a class type.
    pub fn is_class(&self, type_code: &str) -> bool {
        self.class_types.contains(type_code)
    }

    /// Check if a type code represents a logical assertion (as opposed to syntax).
    ///
    /// Logical assertions (typically "|-") denote axioms/theorems asserting logical truths,
    /// while other type codes denote syntax axioms that define term constructors.
    pub fn is_assertion_type(&self, type_code: &str) -> bool {
        self.assertion_type.as_ref() == type_code
    }

    /// Get a Boolean type code for this database.
    ///
    /// Returns the first Boolean type code configured for this database.
    /// For `set.mm`, this is "wff". For `hol.mm`, this is "bool".
    ///
    /// # Returns
    ///
    /// A Boolean type code, or `None` if no Boolean types are configured.
    #[must_use]
    pub fn get_boolean_type(&self) -> Option<Arc<str>> {
        self.boolean_types.iter().next().cloned()
    }
}

/// Information about a constant symbol.
#[derive(Debug, Clone)]
pub struct ConstantInfo {
    /// The constant symbol.
    pub symbol: Arc<str>,
    /// Line number where declared.
    pub line: usize,
    /// Arity (determined from syntax axioms, if applicable).
    pub arity: Option<usize>,
    /// Whether this is a type code constant.
    pub is_type: bool,
}

/// Information about a variable symbol.
#[derive(Debug, Clone)]
pub struct VariableInfo {
    /// The variable symbol.
    pub symbol: Arc<str>,
    /// Line number where declared.
    pub line: usize,
    /// Type code from `$f` statement (if bound).
    pub type_code: Option<Arc<str>>,
    /// Whether the variable is currently active.
    pub active: bool,
}

/// A floating hypothesis (`$f` statement).
#[derive(Debug, Clone)]
pub struct FloatingHyp {
    /// The label for this hypothesis.
    pub label: Label,
    /// The variable being typed.
    pub variable: Arc<str>,
    /// The type code assigned to the variable.
    pub type_code: Arc<str>,
    /// Line number where declared.
    pub line: usize,
}

/// An essential hypothesis (`$e` statement).
#[derive(Debug, Clone)]
pub struct EssentialHyp {
    /// The label for this hypothesis.
    pub label: Label,
    /// The statement (sequence of symbols).
    pub statement: Vec<Arc<str>>,
    /// Line number where declared.
    pub line: usize,
}

/// Syntax analysis for axioms that define term construction.
///
/// This information is computed for axioms where the type code is not the assertion type
/// (typically "|-"). It enables determining arity and slot types for syntax constructors.
#[derive(Debug, Clone)]
pub struct SyntaxInfo {
    /// Distinct variables in order of first appearance.
    /// The length of this vector equals the arity.
    pub distinct_vars: Vec<Arc<str>>,
    /// Constants appearing in the pattern (excluding type code).
    pub constants: HashSet<Arc<str>>,
}

impl SyntaxInfo {
    /// Compute syntax information from an axiom statement.
    ///
    /// # Arguments
    ///
    /// * `statement` - The full axiom statement including type code
    /// * `active_vars` - Variables currently in scope (from parent scopes)
    /// * `type_mapping` - Type configuration to determine assertion type
    ///
    /// # Returns
    ///
    /// `None` if the type code is the assertion type (logical axiom, not syntax axiom)
    #[must_use]
    pub fn from_statement(
        statement: &[Arc<str>],
        active_vars: &HashSet<Arc<str>>,
        type_mapping: &TypeMapping,
    ) -> Option<Self> {
        if statement.is_empty() {
            return None;
        }

        // Check if this is a logical axiom (assertion type, not syntax)
        if type_mapping.is_assertion_type(statement[0].as_ref()) {
            return None;
        }

        let mut distinct_vars = Vec::new();
        let mut seen_vars = HashSet::new();
        let mut constants = HashSet::new();

        // Skip type code (`statement[0]`), process the pattern
        for symbol in statement.iter().skip(1) {
            if active_vars.contains(symbol) {
                // It's a variable
                if seen_vars.insert(symbol.clone()) {
                    // First occurrence of this variable
                    distinct_vars.push(symbol.clone());
                }
            } else {
                // It's a constant
                constants.insert(symbol.clone());
            }
        }

        Some(Self {
            distinct_vars,
            constants,
        })
    }

    /// Get the arity (number of distinct variables).
    #[must_use]
    pub fn arity(&self) -> usize {
        self.distinct_vars.len()
    }
}

/// Core data shared by axioms and theorems.
///
/// In Metamath, both axioms (`$a`) and theorems (`$p`) are assertions that
/// can be used in proofs. This struct contains the fields common to both.
#[derive(Debug, Clone)]
pub struct AssertionCore {
    /// The label for this assertion.
    pub label: Label,
    /// The statement (sequence of symbols).
    pub statement: Vec<Arc<str>>,
    /// Line number where declared.
    pub line: usize,
    /// Mandatory hypotheses (used for proof verification and compressed proof indexing).
    pub hypotheses: (Vec<FloatingHyp>, Vec<EssentialHyp>),
    /// Comment metadata with contributor attributions.
    pub comment: Option<CommentMetadata>,
    /// Distinctness constraints active when this assertion was declared.
    pub distinctness: DistinctnessGraph<DbMetavariable>,
}

impl AssertionCore {
    /// Convert this assertion to a `Statement` for use with symbolic-mgu operations.
    ///
    /// This parses the assertion's statement and hypotheses into `DbTerm` instances
    /// and creates a `Statement` object representing the inference rule.
    ///
    /// # Metamath → symbolic-mgu Mapping
    ///
    /// - **`AssertionCore.statement`** → `Statement.assertion` (conclusion)
    /// - **`EssentialHyp.statement`** → `Statement.hypotheses` (antecedents)
    /// - **`FloatingHyp`** → Used implicitly during parsing for variable typing
    /// - **`AssertionCore.distinctness`** → `Statement.distinctness_graph`
    ///
    /// # Assertion Type Handling
    ///
    /// In Metamath, logical assertions start with "|-" (the provability operator):
    /// - Statement: `["|-", "(", "ph", "->", "ph", ")"]`
    /// - The "|-" is skipped, and the rest is parsed as a Boolean expression
    /// - Result: `DbTerm` representing the wff `(ph -> ph)`
    ///
    /// # Arguments
    ///
    /// * `db` - The Metamath database for symbol lookup and parsing
    ///
    /// # Returns
    ///
    /// A `Statement` representing this assertion as an inference rule.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The statement or hypotheses cannot be parsed
    /// - The resulting terms are not Boolean type
    /// - The Statement validation fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// use std::sync::Arc;
    /// use symbolic_mgu::MguError;
    /// use symbolic_mgu::metamath::{Label, MetamathDatabase, Parser, TypeMapping, MemoryFilesystem};
    ///
    /// # fn example() -> Result<(), MguError> {
    /// // Create and parse a database
    /// let mut fs = MemoryFilesystem::new();
    /// fs.add_file("test.mm", "$c wff $. $v ph $. wph $f wff ph $. ax-1 $a wff ph $.".to_string());
    /// let db_init = MetamathDatabase::new(TypeMapping::set_mm());
    /// let parser = Parser::new(fs, "test.mm", db_init).map_err(|_| MguError::UnificationFailure("parse error".to_string()))?;
    /// let db = parser.parse().map_err(|_| MguError::UnificationFailure("parse error".to_string()))?;
    ///
    /// // Get an axiom and convert to Statement
    /// let label = Label::new("ax-1").map_err(|_| MguError::UnificationFailure("label error".to_string()))?;
    /// let axiom = db.get_axiom(&label).ok_or_else(|| MguError::UnificationFailure("axiom not found".to_string()))?;
    /// let statement = axiom.core.to_statement(&db)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_statement(
        &self,
        db: &Arc<MetamathDatabase>,
    ) -> Result<Statement<DbType, DbMetavariable, DbNode, DbTerm>, MguError> {
        // Parse the conclusion (assertion statement)
        let conclusion = if db.type_mapping().is_assertion_type(&self.statement[0]) {
            // Statement starts with "|-" - skip it and parse rest as Boolean
            let boolean_type =
                db.type_mapping()
                    .get_boolean_type()
                    .ok_or_else(|| MguError::ParseError {
                        location: "assertion".to_string(),
                        message: "No Boolean type configured in database".to_string(),
                    })?;

            // Parse the sequence after "|-" as a Boolean expression
            parse_sequence(&self.statement[1..], &boolean_type, db)?
        } else {
            // Regular statement - parse as-is
            parse_expression(&self.statement, db)?
        };

        // Parse essential hypotheses
        let mut hypothesis_terms = Vec::new();
        for essential_hyp in &self.hypotheses.1 {
            // Essential hypothesis statements also typically start with "|-"
            let hyp_term = if !essential_hyp.statement.is_empty()
                && db
                    .type_mapping()
                    .is_assertion_type(&essential_hyp.statement[0])
            {
                // Skip "|-" and parse rest as Boolean
                let boolean_type =
                    db.type_mapping()
                        .get_boolean_type()
                        .ok_or_else(|| MguError::ParseError {
                            location: "hypothesis".to_string(),
                            message: "No Boolean type configured in database".to_string(),
                        })?;

                parse_sequence(&essential_hyp.statement[1..], &boolean_type, db)?
            } else {
                // Regular hypothesis - parse as-is
                parse_expression(&essential_hyp.statement, db)?
            };

            hypothesis_terms.push(hyp_term);
        }

        // Create the Statement using `new_db_backed()` to avoid calling `Type::try_boolean()`
        // which is unimplemented for `DbType` (requires database context)
        // Note: `FloatingHyp` are used implicitly during parsing for variable type lookup
        Statement::new_db_backed(conclusion, hypothesis_terms, self.distinctness.clone())
    }
}

/// An axiom (`$a` statement).
///
/// All axioms have the format: `LABEL $a TYPE (CONSTANT|VARIABLE)* $.`
/// where TYPE is a constant symbol (e.g., "wff", "class", "|-").
#[derive(Debug, Clone)]
pub struct Axiom {
    /// Core assertion data.
    pub core: AssertionCore,
    /// The type code (first symbol of statement).
    pub type_code: Arc<str>,
    /// Syntax analysis (present for non-"|-" axioms defining term construction).
    pub syntax_info: Option<SyntaxInfo>,
}

/// A theorem (`$p` statement).
#[derive(Debug, Clone)]
pub struct Theorem {
    /// Core assertion data.
    pub core: AssertionCore,
    /// ALL hypotheses that were in scope (for label lookup in compressed proofs).
    /// This includes both mandatory and non-mandatory hypotheses.
    pub all_hypotheses: (Vec<FloatingHyp>, Vec<EssentialHyp>),
    /// Proof in either expanded or compressed format.
    pub proof: Option<Proof>,
}

/// A scope for managing variables, hypotheses, and distinctness constraints.
///
/// Scopes form a parent-child hierarchy using `Arc` for efficient sharing.
/// Variables and hypotheses declared in inner scopes are only visible within
/// that scope and its children.
#[derive(Debug, Clone)]
pub struct Scope {
    /// Parent scope (None for outermost scope).
    parent: Option<Arc<Scope>>,
    /// Variables declared in this scope (not including parent scopes).
    local_variables: HashMap<Arc<str>, VariableInfo>,
    /// Floating hypotheses declared in this scope (preserves insertion order).
    floating_hyps: IndexMap<Label, FloatingHyp>,
    /// Essential hypotheses declared in this scope.
    essential_hyps: Vec<EssentialHyp>,
    /// Distinctness constraints in this scope.
    /// Each tuple represents a pair of variables that must be distinct.
    distinctness: Vec<(Arc<str>, Arc<str>)>,
    /// Fast lookup index for floating hypotheses: (`type_code`, `variable_name`) → `FloatingHyp`
    /// Includes all hypotheses from this scope and parent scopes.
    floating_hyp_index: HashMap<(Arc<str>, Arc<str>), FloatingHyp>,
}

impl Scope {
    /// Create a new outermost scope.
    pub fn new() -> Self {
        Self {
            parent: None,
            local_variables: HashMap::new(),
            floating_hyps: IndexMap::new(),
            essential_hyps: Vec::new(),
            distinctness: Vec::new(),
            floating_hyp_index: HashMap::new(),
        }
    }

    /// Create a child scope with this scope as parent.
    ///
    /// The child scope inherits the parent's floating hypothesis index,
    /// which will be updated as new hypotheses are added to the child scope.
    pub fn new_child(self: &Arc<Self>) -> Self {
        // Start with parent's floating hypothesis index
        let floating_hyp_index = self.floating_hyp_index.clone();

        Self {
            parent: Some(Arc::clone(self)),
            local_variables: HashMap::new(),
            floating_hyps: IndexMap::new(),
            essential_hyps: Vec::new(),
            distinctness: Vec::new(),
            floating_hyp_index,
        }
    }

    /// Declare a variable in this scope.
    ///
    /// # Errors
    ///
    /// Returns `SymbolInUse` if the variable is already declared in this scope.
    pub fn declare_variable(&mut self, info: VariableInfo) -> Result<(), DatabaseError> {
        let symbol = info.symbol.clone();

        // Check if already declared in this scope
        if self.local_variables.contains_key(&symbol) {
            return Err(DatabaseError::SymbolInUse {
                symbol: symbol.to_string(),
                previous_line: self.local_variables[&symbol].line,
            });
        }

        self.local_variables.insert(symbol, info);
        Ok(())
    }

    /// Look up a variable, searching parent scopes if necessary.
    pub fn lookup_variable(&self, symbol: &str) -> Option<&VariableInfo> {
        // Check local scope first
        if let Some(info) = self.local_variables.get(symbol) {
            return Some(info);
        }

        // Search parent scopes
        self.parent
            .as_ref()
            .and_then(|parent| parent.lookup_variable(symbol))
    }

    /// Add a floating hypothesis to this scope.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already used by another floating hypothesis.
    pub fn add_floating_hyp(&mut self, hyp: FloatingHyp) -> Result<(), DatabaseError> {
        let label = hyp.label.clone();

        if self.floating_hyps.contains_key(&label) {
            return Err(DatabaseError::LabelInUse {
                label: label.as_str().to_string(),
                previous_line: self.floating_hyps[&label].line,
            });
        }

        // Add to map
        self.floating_hyps.insert(label, hyp.clone());

        // Update index
        let key = (hyp.type_code.clone(), hyp.variable.clone());
        self.floating_hyp_index.insert(key, hyp);

        Ok(())
    }

    /// Look up floating hypothesis by type code and variable name.
    ///
    /// This uses the pre-built index for O(1) lookup, which already includes
    /// hypotheses from parent scopes.
    ///
    /// # Returns
    ///
    /// The floating hypothesis if found, `None` otherwise.
    pub fn lookup_floating_hyp(
        &self,
        type_code: &str,
        variable_name: &str,
    ) -> Option<&FloatingHyp> {
        let key = (Arc::from(type_code), Arc::from(variable_name));
        self.floating_hyp_index.get(&key)
    }

    /// Add an essential hypothesis to this scope.
    pub fn add_essential_hyp(&mut self, hyp: EssentialHyp) {
        self.essential_hyps.push(hyp);
    }

    /// Add a distinctness constraint to this scope.
    pub fn add_distinctness(&mut self, var1: Arc<str>, var2: Arc<str>) {
        self.distinctness.push((var1, var2));
    }

    /// Look up a floating hypothesis by label in this scope and parent scopes.
    ///
    /// Returns the hypothesis if found, None otherwise.
    pub fn get_floating_hyp(&self, label: &Label) -> Option<FloatingHyp> {
        // Walk up the scope chain
        let mut current = Some(self);
        while let Some(scope) = current {
            if let Some(hyp) = scope.floating_hyps.get(label) {
                return Some(hyp.clone());
            }
            current = scope.parent.as_deref();
        }
        None
    }

    /// Collect all active hypotheses from this scope and parent scopes.
    ///
    /// Returns (`floating_hypotheses`, `essential_hypotheses`).
    pub fn collect_hypotheses(&self) -> (Vec<FloatingHyp>, Vec<EssentialHyp>) {
        // Collect scopes from innermost to outermost
        let mut scopes = Vec::new();
        let mut current = Some(self);
        while let Some(scope) = current {
            scopes.push(scope);
            current = scope.parent.as_deref();
        }

        // Process scopes in reverse order (outermost to innermost)
        // This ensures hypotheses are in declaration order
        let mut floating = Vec::new();
        let mut essential = Vec::new();
        for scope in scopes.iter().rev() {
            floating.extend(scope.floating_hyps.values().cloned());
            essential.extend(scope.essential_hyps.iter().cloned());
        }

        (floating, essential)
    }

    /// Collect only the hypotheses that are relevant to variables in the given statement.
    ///
    /// For an axiom or theorem, only the floating hypotheses for variables that actually
    /// appear in the statement or in essential hypotheses are mandatory. This filters
    /// the full hypothesis list to include only those that are needed.
    pub fn collect_mandatory_hypotheses(
        &self,
        statement: &[Arc<str>],
        active_vars: &HashSet<Arc<str>>,
    ) -> (Vec<FloatingHyp>, Vec<EssentialHyp>) {
        // Get all hypotheses
        let (all_floating, all_essential) = self.collect_hypotheses();

        // Find which variables appear in the statement
        let mut mentioned_vars: HashSet<Arc<str>> = statement
            .iter()
            .filter(|sym| active_vars.contains(*sym))
            .cloned()
            .collect();

        // Also include variables from essential hypotheses
        for ess_hyp in &all_essential {
            for sym in &ess_hyp.statement {
                if active_vars.contains(sym) {
                    mentioned_vars.insert(sym.clone());
                }
            }
        }

        // Filter floating hypotheses to only those for mentioned variables
        let floating: Vec<FloatingHyp> = all_floating
            .into_iter()
            .filter(|hyp| mentioned_vars.contains(&hyp.variable))
            .collect();

        // All essential hypotheses are mandatory
        (floating, all_essential)
    }

    /// Collect all distinctness constraints from this scope and parent scopes.
    ///
    /// Returns a vector of `(variable1, variable2)` pairs.
    pub fn collect_distinctness(&self) -> Vec<(Arc<str>, Arc<str>)> {
        let mut distinctness = Vec::new();

        // Walk up the scope chain
        let mut current = Some(self);
        while let Some(scope) = current {
            // Collect from current scope
            distinctness.extend(scope.distinctness.iter().cloned());

            // Move to parent
            current = scope.parent.as_deref();
        }

        distinctness
    }

    /// Get the set of active variables in this scope and parent scopes.
    pub fn active_variables(&self) -> HashSet<Arc<str>> {
        let mut vars = HashSet::new();

        let mut current = Some(self);
        while let Some(scope) = current {
            for (symbol, info) in &scope.local_variables {
                if info.active {
                    vars.insert(symbol.clone());
                }
            }
            current = scope.parent.as_deref();
        }

        vars
    }
}

impl Default for Scope {
    fn default() -> Self {
        Self::new()
    }
}

/// The main Metamath database structure.
///
/// Manages the parsing state and storage of all Metamath statements,
/// including scoped variables and hypotheses.
///
/// Thread-safe: Implements `Send` and `Sync` to enable concurrent access from multiple threads.
/// Uses `RwLock` for interior mutability, allowing multiple concurrent readers or a single writer.
#[derive(Debug)]
pub struct MetamathDatabase {
    /// Type mapping configuration (immutable).
    type_mapping: TypeMapping,
    /// Global constants (from `$c` statements).
    constants: RwLock<HashMap<Arc<str>, ConstantInfo>>,
    /// Current scope stack (bottom = outermost scope).
    scope_stack: RwLock<Vec<Arc<Scope>>>,
    /// All statement labels used (for detecting duplicates).
    all_labels: RwLock<HashSet<Label>>,
    /// Axioms (global, indexed by label).
    axioms: RwLock<HashMap<Label, Axiom>>,
    /// Theorems (global, indexed by label).
    theorems: RwLock<HashMap<Label, Theorem>>,
    /// Variables grouped by type code for `MetavariableFactory` support.
    /// Maps type code (e.g., `"wff"`, `"setvar"`) to list of variable symbols in order of declaration.
    variables_by_type: RwLock<HashMap<Arc<str>, Vec<Arc<str>>>>,
    /// Bidirectional mapping: variable → (`type_code`, index).
    /// Allows lookup of variable type and index for `DbMetavariable` creation.
    variable_to_type_index: VarMap,
    /// Symbol classification registry: maps symbols to their kind (constant or variable).
    /// Built during parsing of `$c` and `$v` statements.
    symbol_kinds: RwLock<HashMap<Arc<str>, SymbolKind>>,
    /// Syntax axioms indexed by result type for efficient pattern matching.
    /// Built during parsing when syntax axioms are added to the database.
    syntax_axioms_by_type: RwLock<HashMap<Arc<str>, Vec<SyntaxAxiomPattern>>>,
}

impl MetamathDatabase {
    /// Create a new database with the given type mapping.
    pub fn new(type_mapping: TypeMapping) -> Self {
        // Start with one outermost scope
        let initial_scope = Arc::new(Scope::new());

        Self {
            type_mapping,
            constants: RwLock::new(HashMap::new()),
            scope_stack: RwLock::new(vec![initial_scope]),
            all_labels: RwLock::new(HashSet::new()),
            axioms: RwLock::new(HashMap::new()),
            theorems: RwLock::new(HashMap::new()),
            variables_by_type: RwLock::new(HashMap::new()),
            variable_to_type_index: RwLock::new(HashMap::new()),
            symbol_kinds: RwLock::new(HashMap::new()),
            syntax_axioms_by_type: RwLock::new(HashMap::new()),
        }
    }

    /// Get the current (innermost) scope.
    ///
    /// # Panics
    ///
    /// Panics
    /// - if the scope stack is empty (should never happen as there's always a root scope)
    /// - if the `RwLock` was poisoned.
    pub fn current_scope(&self) -> Arc<Scope> {
        self.scope_stack
            .read()
            .expect("RwLock poisoned")
            .last()
            .expect("Scope stack should never be empty")
            .clone()
    }

    /// Push a new scope onto the stack (handle `${` ).
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn push_scope(&self) {
        let parent = self.current_scope();
        let new_scope = Arc::new(parent.new_child());
        self.scope_stack
            .write()
            .expect("RwLock poisoned")
            .push(new_scope);
    }

    /// Pop the current scope from the stack (handle `$}` ).
    ///
    /// # Errors
    ///
    /// Returns `ScopeMismatch` if attempting to pop the outermost scope.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn pop_scope(&self, line: usize) -> Result<(), DatabaseError> {
        if self.scope_stack.read().expect("RwLock poisoned").len() <= 1 {
            return Err(DatabaseError::ScopeMismatch {
                line,
                message: "Attempted to close scope when only outermost scope remains".to_string(),
            });
        }

        self.scope_stack.write().expect("RwLock poisoned").pop();
        Ok(())
    }

    /// Declare a constant (must be in outermost scope).
    ///
    /// # Errors
    ///
    /// Returns `ConstantInInnerScope` if not in the outermost scope, or
    /// `SymbolInUse` if the symbol is already declared as a constant or variable.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn declare_constant(&self, info: ConstantInfo) -> Result<(), DatabaseError> {
        // Constants can only be declared in outermost scope
        if self.scope_stack.read().expect("RwLock poisoned").len() > 1 {
            return Err(DatabaseError::ConstantInInnerScope { line: info.line });
        }

        let symbol = info.symbol.clone();

        // Check if already declared
        {
            let constants = self.constants.read().expect("RwLock poisoned");
            if let Some(existing) = constants.get(&symbol) {
                return Err(DatabaseError::SymbolInUse {
                    symbol: symbol.to_string(),
                    previous_line: existing.line,
                });
            }
        }

        // Check if declared as variable
        if self.current_scope().lookup_variable(&symbol).is_some() {
            return Err(DatabaseError::SymbolInUse {
                symbol: symbol.to_string(),
                previous_line: 0, // Variable line not easily accessible here
            });
        }

        // Register symbol as constant for pattern matching
        self.register_constant_symbol(symbol.clone())?;

        self.constants
            .write()
            .expect("RwLock poisoned")
            .insert(symbol, info);
        Ok(())
    }

    /// Declare a variable in the current scope.
    ///
    /// # Errors
    ///
    /// Returns `SymbolInUse` if the symbol is already declared as a constant or variable.
    ///
    /// # Panics
    ///
    /// Panics
    /// - if the scope stack is empty (should never happen as there's always a root scope)
    /// - if the `RwLock` was poisoned.
    pub fn declare_variable(&self, info: VariableInfo) -> Result<(), DatabaseError> {
        let symbol = info.symbol.clone();

        // Check if it's a constant
        {
            let constants = self.constants.read().expect("RwLock poisoned");
            if let Some(existing) = constants.get(&symbol) {
                return Err(DatabaseError::SymbolInUse {
                    symbol: symbol.to_string(),
                    previous_line: existing.line,
                });
            }
        }

        // Register symbol as variable for pattern matching
        self.register_variable_symbol(symbol.clone())?;

        // Declare in current scope - need to mutate the Arc<Scope>
        let mut scope_stack = self.scope_stack.write().expect("RwLock poisoned");
        let current_scope = scope_stack
            .last_mut()
            .expect("Scope stack should never be empty");

        // Use `Arc::make_mut` to get mutable access
        Arc::make_mut(current_scope).declare_variable(info)
    }

    /// Check if a label is already in use.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn is_label_used(&self, label: &Label) -> bool {
        self.all_labels
            .read()
            .expect("RwLock poisoned")
            .contains(label)
    }

    /// Register a label as used.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already registered.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn register_label(&self, label: Label) -> Result<(), DatabaseError> {
        if self
            .all_labels
            .read()
            .expect("RwLock poisoned")
            .contains(&label)
        {
            return Err(DatabaseError::LabelInUse {
                label: label.as_str().to_string(),
                previous_line: 0, // Would need to track this
            });
        }

        self.all_labels
            .write()
            .expect("RwLock poisoned")
            .insert(label);
        Ok(())
    }

    /// Get the type mapping.
    pub fn type_mapping(&self) -> &TypeMapping {
        &self.type_mapping
    }

    /// Add a floating hypothesis to the current scope.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already registered.
    ///
    /// # Panics
    ///
    /// Panics
    /// - if the scope stack is empty (should never happen as there's always a root scope)
    /// - if the `RwLock` was poisoned.
    pub fn add_floating_hyp(&self, hyp: FloatingHyp) -> Result<(), DatabaseError> {
        self.register_label(hyp.label.clone())?;

        // Mutate current scope
        let mut scope_stack = self.scope_stack.write().expect("RwLock poisoned");
        let current_scope = scope_stack
            .last_mut()
            .expect("Scope stack should never be empty");
        Arc::make_mut(current_scope).add_floating_hyp(hyp)
    }

    /// Add an essential hypothesis to the current scope.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already registered.
    ///
    /// # Panics
    ///
    /// Panics
    /// - if the scope stack is empty (should never happen as there's always a root scope)
    /// - if the `RwLock` was poisoned.
    pub fn add_essential_hyp(&self, hyp: EssentialHyp) -> Result<(), DatabaseError> {
        self.register_label(hyp.label.clone())?;

        // Mutate current scope
        let mut scope_stack = self.scope_stack.write().expect("RwLock poisoned");
        let current_scope = scope_stack
            .last_mut()
            .expect("Scope stack should never be empty");
        Arc::make_mut(current_scope).add_essential_hyp(hyp);
        Ok(())
    }

    /// Add a distinctness constraint to the current scope.
    ///
    /// # Panics
    ///
    /// Panics
    /// - if the scope stack is empty (should never happen as there's always a root scope)
    /// - if the `RwLock` was poisoned.
    pub fn add_distinctness(&self, var1: Arc<str>, var2: Arc<str>) {
        // Mutate current scope
        let mut scope_stack = self.scope_stack.write().expect("RwLock poisoned");
        let current_scope = scope_stack
            .last_mut()
            .expect("Scope stack should never be empty");
        Arc::make_mut(current_scope).add_distinctness(var1, var2);
    }

    /// Add an axiom to the database.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already registered.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn add_axiom(&self, axiom: Axiom) -> Result<(), DatabaseError> {
        let label = axiom.core.label.clone();
        self.register_label(label.clone())?;

        {
            let axioms = self.axioms.read().expect("RwLock poisoned");
            if let Some(existing) = axioms.get(&label) {
                return Err(DatabaseError::LabelInUse {
                    label: label.as_str().to_string(),
                    previous_line: existing.core.line,
                });
            }
        }

        // Index syntax axiom for pattern matching (before inserting, so we can borrow)
        self.index_syntax_axiom(&axiom);

        self.axioms
            .write()
            .expect("RwLock poisoned")
            .insert(label, axiom);
        Ok(())
    }

    /// Add a theorem to the database.
    ///
    /// # Errors
    ///
    /// Returns `LabelInUse` if the label is already registered.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn add_theorem(&self, theorem: Theorem) -> Result<(), DatabaseError> {
        let label = theorem.core.label.clone();
        self.register_label(label.clone())?;

        {
            let theorems = self.theorems.read().expect("RwLock poisoned");
            if let Some(existing) = theorems.get(&label) {
                return Err(DatabaseError::LabelInUse {
                    label: label.as_str().to_string(),
                    previous_line: existing.core.line,
                });
            }
        }

        self.theorems
            .write()
            .expect("RwLock poisoned")
            .insert(label, theorem);
        Ok(())
    }

    /// Get an axiom by label.
    ///
    /// Returns a clone of the axiom if it exists.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn get_axiom(&self, label: &Label) -> Option<Axiom> {
        self.axioms
            .read()
            .expect("RwLock poisoned")
            .get(label)
            .cloned()
    }

    /// Get a theorem by label.
    ///
    /// Returns a clone of the theorem if it exists.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn get_theorem(&self, label: &Label) -> Option<Theorem> {
        self.theorems
            .read()
            .expect("RwLock poisoned")
            .get(label)
            .cloned()
    }

    /// Check if a label exists in the database (as axiom, theorem, or hypothesis).
    ///
    /// This is used during proof parsing to validate label references.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn label_exists(&self, label: &str) -> bool {
        // Try to parse as a Label first
        let Ok(label_obj) = Label::from_encoded(label) else {
            return false;
        };

        // Check axioms and theorems
        if self
            .axioms
            .read()
            .expect("RwLock poisoned")
            .contains_key(&label_obj)
            || self
                .theorems
                .read()
                .expect("RwLock poisoned")
                .contains_key(&label_obj)
        {
            return true;
        }

        // Check hypotheses in current scope
        let (floating, essential) = self.current_scope().collect_hypotheses();
        floating.iter().any(|h| h.label == label_obj)
            || essential.iter().any(|h| h.label == label_obj)
    }

    /// Get all axioms.
    ///
    /// Returns a cloned `HashMap` of all axioms.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn axioms(&self) -> HashMap<Label, Axiom> {
        self.axioms.read().expect("RwLock poisoned").clone()
    }

    /// Get all theorems.
    ///
    /// Returns a cloned `HashMap` of all theorems.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn theorems(&self) -> HashMap<Label, Theorem> {
        self.theorems.read().expect("RwLock poisoned").clone()
    }

    /// Register a variable with its type code.
    ///
    /// This is called when a floating hypothesis (`$f` statement) is encountered.
    /// Variables are tracked in order of declaration for `MetavariableFactory` support.
    ///
    /// # Behavior
    /// - **Idempotent**: Re-registering a variable with the same type has no side effects
    /// - **Type consistency**: Returns error if variable already registered with different type
    /// - **First registration**: Assigns the next available index for the type
    ///
    /// # Errors
    /// Returns `DatabaseError::TypeConflict` if the variable is already registered with a different type.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn register_variable_type(
        &self,
        type_code: Arc<str>,
        variable: Arc<str>,
        line: usize,
    ) -> Result<(), DatabaseError> {
        // Check if variable already registered
        {
            let var_to_type = self.variable_to_type_index.read().expect("RwLock poisoned");
            if let Some((existing_type, _existing_index)) = var_to_type.get(&variable) {
                if existing_type.as_ref() != type_code.as_ref() {
                    return Err(DatabaseError::TypeConflict {
                        symbol: variable.to_string(),
                        existing_type: existing_type.to_string(),
                        new_type: type_code.to_string(),
                        line,
                    });
                }
                // Idempotent: same type, do nothing
                return Ok(());
            }
        }

        // First registration: assign index and add to maps
        let mut vars_by_type = self.variables_by_type.write().expect("RwLock poisoned");
        let type_vars = vars_by_type.entry(type_code.clone()).or_default();

        let index = type_vars.len();
        type_vars.push(variable.clone());

        self.variable_to_type_index
            .write()
            .expect("RwLock poisoned")
            .insert(variable, (type_code, index));

        Ok(())
    }

    /// Get all variables of a given type in order of declaration.
    ///
    /// Returns a cloned vector if variables of this type exist, otherwise an empty vector.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn variables_of_type(&self, type_code: &str) -> Vec<Arc<str>> {
        self.variables_by_type
            .read()
            .expect("RwLock poisoned")
            .get(type_code)
            .cloned()
            .unwrap_or_default()
    }

    /// Look up the type and index for a variable.
    ///
    /// Returns `None` if the variable has not been registered via a floating hypothesis.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn variable_type_and_index(&self, variable: &str) -> Option<(Arc<str>, usize)> {
        self.variable_to_type_index
            .read()
            .expect("RwLock poisoned")
            .get(variable)
            .map(|(t, i)| (t.clone(), *i))
    }

    /// Look up the type code for a variable.
    ///
    /// Returns `None` if the variable has not been registered via a floating hypothesis.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn variable_type(&self, variable: &str) -> Option<Arc<str>> {
        self.variable_to_type_index
            .read()
            .expect("RwLock poisoned")
            .get(variable)
            .map(|(t, _)| t.clone())
    }

    /// Check if a symbol is a registered variable.
    ///
    /// Returns `true` if the symbol has been registered via a floating hypothesis.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn is_variable(&self, symbol: &str) -> bool {
        self.variable_to_type_index
            .read()
            .expect("RwLock poisoned")
            .contains_key(symbol)
    }

    /// Get all active variables in the current scope.
    ///
    /// Returns the set of variables that are currently in scope (including parent scopes).
    pub fn active_variables(&self) -> HashSet<Arc<str>> {
        self.current_scope().active_variables()
    }

    /// Look up a floating hypothesis by label.
    ///
    /// Searches the current scope and all parent scopes for a floating hypothesis
    /// with the given label.
    pub fn get_floating_hyp(&self, label: &Label) -> Option<FloatingHyp> {
        self.current_scope().get_floating_hyp(label)
    }

    /// Look up a floating hypothesis by type code and variable name.
    ///
    /// Uses the current scope's pre-built index for O(1) lookup.
    ///
    /// # Returns
    ///
    /// A clone of the floating hypothesis if found, `None` otherwise.
    pub fn lookup_floating_hyp(&self, type_code: &str, variable_name: &str) -> Option<FloatingHyp> {
        self.current_scope()
            .lookup_floating_hyp(type_code, variable_name)
            .cloned()
    }

    /// Build a `DistinctnessGraph` for variables mentioned in a statement.
    ///
    /// This collects all distinctness constraints from the current scope and filters
    /// them to only include pairs where both variables are in the provided set.
    ///
    /// # Arguments
    ///
    /// * `variables` - Set of variable names mentioned in the statement
    /// * `db_arc` - Arc reference to this database (needed to create `DbMetavariable` instances)
    ///
    /// # Returns
    ///
    /// A `DistinctnessGraph` containing only the variables from the input set.
    pub fn build_distinctness_graph(
        &self,
        variables: &HashSet<Arc<str>>,
        db_arc: &Arc<MetamathDatabase>,
    ) -> DistinctnessGraph<DbMetavariable> {
        let mut graph = DistinctnessGraph::new();
        let factory = DbMetavariableFactory::new(Arc::clone(db_arc));

        // Collect all distinctness constraints from scope
        let all_distinctness = self.current_scope().collect_distinctness();

        // Filter to only pairs where both variables are mentioned in the statement
        for (var1, var2) in all_distinctness {
            if variables.contains(&var1) && variables.contains(&var2) {
                // Convert variable names to `DbMetavariable`
                if let (Ok(mv1), Ok(mv2)) =
                    (factory.create_by_name(&var1), factory.create_by_name(&var2))
                {
                    // Add edge to graph (ignore errors - edge might already exist)
                    let _ = graph.add_edge(&mv1, &mv2);
                }
            }
        }

        graph
    }

    /// Register a symbol as a constant (from `$c` statement).
    ///
    /// # Errors
    ///
    /// Returns `IllegalSymbol` if the symbol is already registered as a variable.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn register_constant_symbol(&self, symbol: Arc<str>) -> Result<(), DatabaseError> {
        let mut kinds = self.symbol_kinds.write().expect("RwLock poisoned");

        // Check if already declared as variable
        if let Some(SymbolKind::Variable) = kinds.get(&symbol) {
            return Err(DatabaseError::IllegalSymbol {
                symbol: symbol.to_string(),
                reason: "Already declared as variable".to_string(),
            });
        }

        kinds.insert(symbol, SymbolKind::Constant);
        Ok(())
    }

    /// Register a symbol as a variable (from `$v` statement).
    ///
    /// # Errors
    ///
    /// Returns `IllegalSymbol` if the symbol is already registered as a constant.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn register_variable_symbol(&self, symbol: Arc<str>) -> Result<(), DatabaseError> {
        let mut kinds = self.symbol_kinds.write().expect("RwLock poisoned");

        // Check if already declared as constant
        if let Some(SymbolKind::Constant) = kinds.get(&symbol) {
            return Err(DatabaseError::IllegalSymbol {
                symbol: symbol.to_string(),
                reason: "Already declared as constant".to_string(),
            });
        }

        kinds.insert(symbol, SymbolKind::Variable);
        Ok(())
    }

    /// Get the kind of a symbol (constant or variable).
    ///
    /// Returns `None` if the symbol has not been declared.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn symbol_kind(&self, symbol: &str) -> Option<SymbolKind> {
        self.symbol_kinds
            .read()
            .expect("RwLock poisoned")
            .get(symbol)
            .copied()
    }

    /// Check if a symbol is a constant.
    ///
    /// Returns `false` if the symbol has not been declared.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn is_constant(&self, symbol: &str) -> bool {
        matches!(self.symbol_kind(symbol), Some(SymbolKind::Constant))
    }

    /// Check if a symbol is a variable (declared with `$v`).
    ///
    /// Note: This checks if the symbol was declared as a variable with `$v`,
    /// not whether it has been bound to a type via `$f`. Use `variable_type()`
    /// to check if a variable has a type binding.
    ///
    /// Returns `false` if the symbol has not been declared.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn is_variable_symbol(&self, symbol: &str) -> bool {
        matches!(self.symbol_kind(symbol), Some(SymbolKind::Variable))
    }

    /// Index a syntax axiom for pattern matching.
    ///
    /// This should be called when adding a syntax axiom to the database.
    /// It pre-processes the axiom into a pattern with matching hints and stores it
    /// indexed by result type.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn index_syntax_axiom(&self, axiom: &Axiom) {
        // Only index syntax axioms
        if let Some(pattern) = SyntaxAxiomPattern::from_axiom(axiom, self) {
            self.syntax_axioms_by_type
                .write()
                .expect("RwLock poisoned")
                .entry(pattern.type_code.clone())
                .or_default()
                .push(pattern);
        }
    }

    /// Get syntax axioms for a given result type.
    ///
    /// Returns a cloned vector of all syntax axiom patterns that produce
    /// the given type.
    ///
    /// # Panics
    ///
    /// Panics if the `RwLock` was poisoned.
    pub fn get_syntax_axioms_for_type(&self, type_code: &str) -> Vec<SyntaxAxiomPattern> {
        self.syntax_axioms_by_type
            .read()
            .expect("RwLock poisoned")
            .get(type_code)
            .cloned()
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile-time assertion that `MetamathDatabase` is Send and Sync
    #[test]
    fn assert_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}
        is_send::<MetamathDatabase>();
        is_sync::<MetamathDatabase>();
    }

    #[test]
    fn type_mapping_set_mm() {
        let mapping = TypeMapping::set_mm();
        assert!(mapping.is_boolean("wff"));
        assert!(mapping.is_setvar("setvar"));
        assert!(mapping.is_class("class"));
        assert!(!mapping.is_boolean("class"));
    }

    #[test]
    fn type_mapping_hol_mm() {
        let mapping = TypeMapping::hol_mm();
        assert!(mapping.is_boolean("bool"));
        assert!(!mapping.is_setvar("bool"));
        assert!(!mapping.is_class("bool"));
    }

    #[test]
    fn scope_variable_declaration() {
        let mut scope = Scope::new();

        let var = VariableInfo {
            symbol: Arc::from("x"),
            line: 1,
            type_code: None,
            active: true,
        };

        // First declaration should succeed
        assert!(scope.declare_variable(var.clone()).is_ok());

        // Duplicate declaration should fail
        let result = scope.declare_variable(var);
        assert!(matches!(result, Err(DatabaseError::SymbolInUse { .. })));
    }

    #[test]
    fn scope_variable_lookup() {
        let parent = Arc::new({
            let mut scope = Scope::new();
            scope
                .declare_variable(VariableInfo {
                    symbol: Arc::from("x"),
                    line: 1,
                    type_code: None,
                    active: true,
                })
                .unwrap();
            scope
        });

        let mut child = parent.new_child();
        child
            .declare_variable(VariableInfo {
                symbol: Arc::from("y"),
                line: 2,
                type_code: None,
                active: true,
            })
            .unwrap();

        // Can find variable in current scope
        assert!(child.lookup_variable("y").is_some());

        // Can find variable in parent scope
        assert!(child.lookup_variable("x").is_some());

        // Cannot find undeclared variable
        assert!(child.lookup_variable("z").is_none());
    }

    #[test]
    fn floating_hyp_index_lookup() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        // Add a floating hypothesis
        let hyp = FloatingHyp {
            label: Label::new("fph").unwrap(),
            variable: Arc::from("ph"),
            type_code: Arc::from("wff"),
            line: 1,
        };
        db.add_floating_hyp(hyp.clone()).unwrap();

        // Look up by type and variable name
        let found = db.lookup_floating_hyp("wff", "ph");
        assert!(found.is_some());
        assert_eq!(found.unwrap().label, hyp.label);

        // Look up with wrong type
        let not_found = db.lookup_floating_hyp("setvar", "ph");
        assert!(not_found.is_none());

        // Look up unknown variable
        let not_found = db.lookup_floating_hyp("wff", "ps");
        assert!(not_found.is_none());
    }

    #[test]
    fn floating_hyp_index_inheritance() {
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        // Add hypothesis in outer scope
        let hyp1 = FloatingHyp {
            label: Label::new("fph").unwrap(),
            variable: Arc::from("ph"),
            type_code: Arc::from("wff"),
            line: 1,
        };
        db.add_floating_hyp(hyp1.clone()).unwrap();

        // Push new scope
        db.push_scope();

        // Should still find parent scope's hypothesis
        let found = db.lookup_floating_hyp("wff", "ph");
        assert!(found.is_some());
        assert_eq!(found.unwrap().label, hyp1.label);

        // Add hypothesis in inner scope
        let hyp2 = FloatingHyp {
            label: Label::new("fps").unwrap(),
            variable: Arc::from("ps"),
            type_code: Arc::from("wff"),
            line: 2,
        };
        db.add_floating_hyp(hyp2.clone()).unwrap();

        // Should find both hypotheses
        assert!(db.lookup_floating_hyp("wff", "ph").is_some());
        assert!(db.lookup_floating_hyp("wff", "ps").is_some());

        // Pop scope
        db.pop_scope(3).unwrap();

        // Should still find outer hypothesis
        assert!(db.lookup_floating_hyp("wff", "ph").is_some());

        // Should NOT find inner hypothesis
        assert!(db.lookup_floating_hyp("wff", "ps").is_none());
    }

    #[test]
    fn scope_hypothesis_collection() {
        let parent = Arc::new({
            let mut scope = Scope::new();
            scope
                .add_floating_hyp(FloatingHyp {
                    label: Label::new("fx").unwrap(),
                    variable: Arc::from("x"),
                    type_code: Arc::from("wff"),
                    line: 1,
                })
                .unwrap();
            scope
        });

        let mut child = parent.new_child();
        child
            .add_floating_hyp(FloatingHyp {
                label: Label::new("fy").unwrap(),
                variable: Arc::from("y"),
                type_code: Arc::from("setvar"),
                line: 2,
            })
            .unwrap();

        let (floating, _essential) = child.collect_hypotheses();

        // Should have both parent and child hypotheses
        assert_eq!(floating.len(), 2);
    }

    #[test]
    fn database_creation() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        assert_eq!(db.scope_stack.read().expect("RwLock poisoned").len(), 1); // Should start with outermost scope
        assert_eq!(db.constants.read().expect("RwLock poisoned").len(), 0);
    }

    #[test]
    fn database_constant_declaration() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        let const_info = ConstantInfo {
            symbol: Arc::from("wff"),
            line: 1,
            arity: None,
            is_type: true,
        };

        // Should succeed in outermost scope
        assert!(db.declare_constant(const_info).is_ok());

        // Duplicate should fail
        let dup = ConstantInfo {
            symbol: Arc::from("wff"),
            line: 2,
            arity: None,
            is_type: true,
        };
        assert!(matches!(
            db.declare_constant(dup),
            Err(DatabaseError::SymbolInUse { .. })
        ));
    }

    #[test]
    fn database_constant_in_inner_scope() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Push a scope
        db.push_scope();

        let const_info = ConstantInfo {
            symbol: Arc::from("wff"),
            line: 1,
            arity: None,
            is_type: true,
        };

        // Should fail in inner scope
        assert!(matches!(
            db.declare_constant(const_info),
            Err(DatabaseError::ConstantInInnerScope { .. })
        ));
    }

    #[test]
    fn database_variable_declaration() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        let var_info = VariableInfo {
            symbol: Arc::from("x"),
            line: 1,
            type_code: None,
            active: true,
        };

        assert!(db.declare_variable(var_info).is_ok());

        // Duplicate in same scope should fail
        let dup = VariableInfo {
            symbol: Arc::from("x"),
            line: 2,
            type_code: None,
            active: true,
        };
        assert!(matches!(
            db.declare_variable(dup),
            Err(DatabaseError::SymbolInUse { .. })
        ));
    }

    #[test]
    fn database_scope_push_pop() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        assert_eq!(db.scope_stack.read().expect("RwLock poisoned").len(), 1);

        db.push_scope();
        assert_eq!(db.scope_stack.read().expect("RwLock poisoned").len(), 2);

        assert!(db.pop_scope(1).is_ok());
        assert_eq!(db.scope_stack.read().expect("RwLock poisoned").len(), 1);

        // Popping outermost scope should fail
        assert!(matches!(
            db.pop_scope(2),
            Err(DatabaseError::ScopeMismatch { .. })
        ));
    }

    #[test]
    fn database_variable_in_nested_scopes() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Declare in outer scope
        db.declare_variable(VariableInfo {
            symbol: Arc::from("x"),
            line: 1,
            type_code: None,
            active: true,
        })
        .unwrap();

        // Push scope and declare different variable
        db.push_scope();
        db.declare_variable(VariableInfo {
            symbol: Arc::from("y"),
            line: 2,
            type_code: None,
            active: true,
        })
        .unwrap();

        // Both should be visible from inner scope
        assert!(db.current_scope().lookup_variable("x").is_some());
        assert!(db.current_scope().lookup_variable("y").is_some());

        // Pop scope
        db.pop_scope(3).unwrap();

        // Only outer variable should be visible
        assert!(db.current_scope().lookup_variable("x").is_some());
        assert!(db.current_scope().lookup_variable("y").is_none());
    }

    #[test]
    fn variable_registration_idempotent() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // First registration
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();

        // Idempotent: same type, no error
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 2)
            .unwrap();

        // Verify only registered once
        let vars = db.variables_of_type("wff");
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].as_ref(), "ph");

        // Verify lookup
        let (type_code, index) = db.variable_type_and_index("ph").unwrap();
        assert_eq!(type_code.as_ref(), "wff");
        assert_eq!(index, 0);
    }

    #[test]
    fn variable_type_conflict() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // First registration
        db.register_variable_type(Arc::from("wff"), Arc::from("x"), 1)
            .unwrap();

        // Type conflict: cannot change type
        let result = db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 2);
        assert!(matches!(result, Err(DatabaseError::TypeConflict { .. })));
    }

    #[test]
    fn symbol_registry_constant() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Register a constant
        db.register_constant_symbol(Arc::from("wff")).unwrap();

        // Check it's recognized as constant
        assert!(db.is_constant("wff"));
        assert!(!db.is_variable_symbol("wff"));
        assert_eq!(db.symbol_kind("wff"), Some(SymbolKind::Constant));

        // Trying to register as variable should fail
        let result = db.register_variable_symbol(Arc::from("wff"));
        assert!(matches!(result, Err(DatabaseError::IllegalSymbol { .. })));
    }

    #[test]
    fn symbol_registry_variable() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Register a variable
        db.register_variable_symbol(Arc::from("ph")).unwrap();

        // Check it's recognized as variable
        assert!(db.is_variable_symbol("ph"));
        assert!(!db.is_constant("ph"));
        assert_eq!(db.symbol_kind("ph"), Some(SymbolKind::Variable));

        // Trying to register as constant should fail
        let result = db.register_constant_symbol(Arc::from("ph"));
        assert!(matches!(result, Err(DatabaseError::IllegalSymbol { .. })));
    }

    #[test]
    fn symbol_registry_idempotent() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Registering the same symbol twice as constant should be idempotent
        db.register_constant_symbol(Arc::from("->")).unwrap();
        db.register_constant_symbol(Arc::from("->")).unwrap();
        assert!(db.is_constant("->"));

        // Same for variables
        db.register_variable_symbol(Arc::from("x")).unwrap();
        db.register_variable_symbol(Arc::from("x")).unwrap();
        assert!(db.is_variable_symbol("x"));
    }

    #[test]
    fn symbol_registry_unknown() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Unknown symbol should return None/false
        assert_eq!(db.symbol_kind("unknown"), None);
        assert!(!db.is_constant("unknown"));
        assert!(!db.is_variable_symbol("unknown"));
    }

    #[test]
    fn variable_indices_by_type() {
        let db = MetamathDatabase::new(TypeMapping::set_mm());

        // Register multiple variables of same type
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ch"), 3)
            .unwrap();

        // Register variables of different type
        db.register_variable_type(Arc::from("setvar"), Arc::from("x"), 4)
            .unwrap();
        db.register_variable_type(Arc::from("setvar"), Arc::from("y"), 5)
            .unwrap();

        // Verify indices are assigned in order
        assert_eq!(
            db.variable_type_and_index("ph"),
            Some((Arc::from("wff"), 0))
        );
        assert_eq!(
            db.variable_type_and_index("ps"),
            Some((Arc::from("wff"), 1))
        );
        assert_eq!(
            db.variable_type_and_index("ch"),
            Some((Arc::from("wff"), 2))
        );
        assert_eq!(
            db.variable_type_and_index("x"),
            Some((Arc::from("setvar"), 0))
        );
        assert_eq!(
            db.variable_type_and_index("y"),
            Some((Arc::from("setvar"), 1))
        );

        // Verify by-type lists
        let wff_vars = db.variables_of_type("wff");
        assert_eq!(wff_vars.len(), 3);
        assert_eq!(wff_vars[0].as_ref(), "ph");
        assert_eq!(wff_vars[1].as_ref(), "ps");
        assert_eq!(wff_vars[2].as_ref(), "ch");

        let setvar_vars = db.variables_of_type("setvar");
        assert_eq!(setvar_vars.len(), 2);
        assert_eq!(setvar_vars[0].as_ref(), "x");
        assert_eq!(setvar_vars[1].as_ref(), "y");
    }
}
