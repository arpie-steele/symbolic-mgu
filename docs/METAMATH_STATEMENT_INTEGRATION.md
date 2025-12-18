# Metamath Statement Integration

**Status**: Phases 1-4 Complete (v0.1.0-alpha.15)
**Planned**: 2025-12-15
**Completed**: 2025-12-17
**Purpose**: Integration between `metamath::AssertionCore` and `Statement` for unification-based proof discovery

## Implementation Status

**✅ COMPLETE** - Core functionality fully implemented and tested:
- **Phase 1**: Term parsing (Metamath expressions → `DbTerm`)
- **Phase 2**: Statement conversion (`AssertionCore` → `Statement`)
- **Phase 3**: Basic proof building (substitutions → expanded proofs)
- **Phase 4**: Advanced proof building (APPLY, CONDENSED_DETACH proofs)

**📊 Test Coverage**:
- 10 integration tests for expression parsing
- 6 integration tests for statement conversion
- 7 integration tests for proof building
- All quality gates passing (test, clippy, doc, fmt)

**⏳ DEFERRED**:
- Essential hypotheses requiring recursive proof search (complex, requires theorem prover)
- Proof length optimization (not critical for correctness)
- Term caching with OnceLock (performance optimization)
- Compressed proof generation (Phase 5, explicitly optional)

See "Future Enhancements" section below for details.

## Overview

This document describes the integration between the Metamath database parser and the core symbolic-mgu proof operations. The implementation achieves:

1. Create `Statement<DbType, DbMetavariable, DbNode, DbTerm>` objects from Metamath `AssertionCore` (shared by `Axiom` and `Theorem`)
2. Convert unification results (`Substitution`) back to Metamath proof format (expanded label sequences)

This enables using symbolic-mgu's unification engine to discover novel substitutions between Metamath assertions, going beyond what's recorded in existing proofs.

## Completed Implementation

### Phase 1: Term Parsing (src/metamath/expr_parser.rs)

**Implemented**:
- `parse_expression()` - Parses Metamath symbol sequences to `DbTerm`
- `parse_sequence()` - Recursive parser for nested expressions
- Symbol classification via `SymbolKind` enum (Constant vs Variable)
- Pattern matching with `SyntaxAxiomPattern`, `PatternElement`, `PatternHints`
- Floating hypothesis indexing for O(1) variable type lookups
- Type checking during parse

**Tests**: `tests/metamath_expression_parsing.rs` (10 tests)

### Phase 2: Statement Conversion (src/metamath/database.rs)

**Implemented**:
- `AssertionCore::to_statement()` - Converts Metamath assertions to `Statement` objects
- Hypothesis parsing (both floating and essential)
- Distinctness graph conversion from `$d` statements
- Type validation (ensures Boolean assertions)
- Support for both `Axiom` and `Theorem` via shared `AssertionCore`

**Tests**: `tests/metamath_statement_conversion.rs` (6 tests)

### Phase 3: Basic Proof Building (src/metamath/proof_builder.rs)

**Implemented**:
- `ProofBuilder` struct with database reference
- `ProofBuilder::build_proof()` - Generates expanded proofs from substitutions
- `build_term_steps()` - Recursive helper for term construction
- Maps variables to floating hypothesis labels
- Builds proof steps in RPN (Reverse Polish Notation) for Metamath's stack model
- Error types: `ProofBuildError` with specific error variants

**Partial**: Essential hypotheses acknowledged but deferred (requires recursive proof search)

**Tests**: `tests/metamath_proof_building.rs` (7 tests)

### Phase 4: Advanced Proof Building (src/metamath/proof_builder.rs)

**Implemented**:
- `ProofBuilder::build_application_proof()` - Generates modus ponens proofs for APPLY
- `ProofBuilder::build_condensed_detachment_proof()` - Generates proofs for CONDENSED_DETACH
- Both use ax-mp (modus ponens) as the inference rule
- Handle complex substitutions with multiple variables

**Not Implemented**: Proof length optimization (not critical for correctness)

**Tests**: Included in `tests/metamath_proof_building.rs`

### Type System (src/metamath/symbolic.rs)

**Implemented**:
- `DbType` - Maps Metamath type codes to `Type` trait
- `DbMetavariable` - Maps Metamath variables to `Metavariable` trait
- `DbNode` - Maps Metamath syntax axioms to `Node` trait
- `DbTerm` - Type alias for `EnumTerm<DbType, DbMetavariable, DbNode>`
- `DbMetavariableFactory` - Factory for creating database-backed metavariables
- All types hold `Arc<MetamathDatabase>` references

**Not Implemented**: Convenience type aliases (`DbStatement`, `DbSubstitution`, `DbTermFactory`)

## User Requirements

From discussion:

1. **Term Type**: Use `pub type DbTerm = EnumTerm<DbType, DbMetavariable, DbNode>` rather than creating a new wrapper type
   - The type parameters already hold `Arc<MetamathDatabase>` references
   - No need for additional wrapping layer

2. **Proof Format**: Expanded proofs initially, compressed proofs as future enhancement
   - Focus: Generate label sequences from substitutions
   - Defer: Compressed proof generation

3. **Scope**: Support both `Axiom` and `Theorem` via their shared `AssertionCore`
   - Assertions with type codes (e.g., `"|-"`) that don't correspond to variables
   - Perfect match for unification targets

4. **Novel Discovery Focus**: The goal is finding *new* substitutions, not reproducing existing proofs
   - Use unification to discover relationships between any pair/sequence of assertions
   - Don't constrain ourselves to what's already in theorem proofs
   - More general substitutions are desirable (could lead to shorter proofs)

## Architecture Components

### 1. Type Aliases

Add to `src/metamath/symbolic.rs`:

```rust
use crate::term::simple::EnumTerm;
use crate::term::factory::EnumTermFactory;

/// Term type backed by Metamath database.
///
/// Uses `EnumTerm` parameterized with database-backed types.
/// The `Arc<MetamathDatabase>` references are held within `DbType`,
/// `DbMetavariable`, and `DbNode`, avoiding the need for a wrapper type.
pub type DbTerm = EnumTerm<DbType, DbMetavariable, DbNode>;

/// Term factory for creating `DbTerm` instances.
pub type DbTermFactory = EnumTermFactory<DbType, DbMetavariable, DbNode>;

/// Statement type backed by Metamath database.
pub type DbStatement = Statement<DbType, DbMetavariable, DbNode, DbTerm>;

/// Substitution type for database-backed terms.
pub type DbSubstitution = Substitution<DbMetavariable, DbTerm>;
```

### 2. AssertionCore to Statement Conversion

Add to `src/metamath/database.rs`:

```rust
impl AssertionCore {
    /// Convert this assertion to a `Statement` for use with unification.
    ///
    /// This enables using symbolic-mgu's proof operations (APPLY, CONTRACT,
    /// CONDENSED_DETACH) with Metamath assertions.
    ///
    /// # Arguments
    ///
    /// * `db_arc` - Shared reference to the database (needed for creating
    ///              `DbType`, `DbMetavariable`, `DbNode`)
    ///
    /// # Returns
    ///
    /// A `DbStatement` with:
    /// - Assertion: The main statement (e.g., `|- ( ph -> ( ps -> ph ) )`)
    /// - Hypotheses: Essential hypotheses from scope (e.g., `|- ph`, `|- ps`)
    /// - Distinctness: Graph of variable constraints from `$d` statements
    ///
    /// # Errors
    ///
    /// Returns `MguError` if:
    /// - Statement parsing fails (malformed expression)
    /// - Type checking fails (non-Boolean assertion)
    /// - Term construction fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// use symbolic_mgu::metamath::{MetamathDatabase, TypeMapping, Parser, StdFilesystem};
    /// use std::sync::Arc;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// // ... parse database ...
    ///
    /// let axiom = db.get_axiom(&"ax-1".parse()?).unwrap();
    /// let stmt = axiom.core.to_statement(&db)?;
    ///
    /// // Now can use with unification operations
    /// // let result = stmt.apply(...)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_statement(
        &self,
        db_arc: &Arc<MetamathDatabase>,
    ) -> Result<DbStatement, MguError> {
        todo!("Parse statement vector to DbTerm, construct Statement")
    }
}

impl Axiom {
    /// Convenience method: convert axiom's assertion to Statement.
    ///
    /// Delegates to `core.to_statement(db_arc)`.
    pub fn to_statement(&self, db_arc: &Arc<MetamathDatabase>) -> Result<DbStatement, MguError> {
        self.core.to_statement(db_arc)
    }
}

impl Theorem {
    /// Convenience method: convert theorem's assertion to Statement.
    ///
    /// Delegates to `core.to_statement(db_arc)`.
    pub fn to_statement(&self, db_arc: &Arc<MetamathDatabase>) -> Result<DbStatement, MguError> {
        self.core.to_statement(db_arc)
    }
}
```

### 3. Substitution to Metamath Proof

Add new module `src/metamath/proof_builder.rs`:

```rust
//! Convert unification results to Metamath proof format.
//!
//! This module provides tools for generating Metamath proofs from
//! unification substitutions discovered by symbolic-mgu operations.

use crate::metamath::database::MetamathDatabase;
use crate::metamath::label::Label;
use crate::metamath::proof::Proof;
use crate::metamath::symbolic::{DbMetavariable, DbTerm, DbSubstitution};
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during proof building.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ProofBuildError {
    /// Variable in substitution not found in database.
    #[error("Variable '{variable}' not found in database")]
    VariableNotFound { variable: String },

    /// Cannot represent term in Metamath proof format.
    #[error("Term cannot be represented in Metamath format: {reason}")]
    UnrepresentableTerm { reason: String },

    /// Missing required hypothesis.
    #[error("Required hypothesis '{label}' not found")]
    MissingHypothesis { label: String },
}

/// Builder for constructing Metamath proofs from unification results.
///
/// # Purpose
///
/// When symbolic-mgu discovers a unification between statements, we want to
/// record this as a Metamath proof. This builder converts:
///
/// - A `Substitution<DbMetavariable, DbTerm>` from unification
/// - Into a `Proof` (expanded label sequence)
///
/// # Example Use Case
///
/// ```text
/// Given:
///   ax-1: |- ( ph -> ( ps -> ph ) )
///   ax-2: |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )
///
/// Find unification of ax-1 with consequent of ax-2:
///   σ = { ph ↦ (ψ → χ), ps ↦ ψ }
///
/// Generate proof showing:
///   |- ( (ψ → χ) -> (ψ -> (ψ → χ)) )
///
/// Proof: [ax-1, float_hyp_psi, float_hyp_chi]
/// ```
pub struct ProofBuilder {
    /// Reference to database for variable/hypothesis lookups.
    database: Arc<MetamathDatabase>,
}

impl ProofBuilder {
    /// Create a new proof builder.
    pub fn new(database: Arc<MetamathDatabase>) -> Self {
        Self { database }
    }

    /// Build an expanded proof from a substitution.
    ///
    /// # Arguments
    ///
    /// * `assertion_label` - The axiom/theorem being instantiated
    /// * `substitution` - The substitution from unification
    ///
    /// # Returns
    ///
    /// An expanded `Proof` consisting of:
    /// 1. Floating hypotheses for each variable in domain of substitution
    /// 2. Essential hypotheses (if any) with substitution applied
    /// 3. The assertion label
    ///
    /// # Errors
    ///
    /// Returns error if substitution contains variables not in database,
    /// or if terms cannot be represented in Metamath format.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use symbolic_mgu::metamath::{MetamathDatabase, TypeMapping};
    /// use symbolic_mgu::metamath::proof_builder::ProofBuilder;
    /// use std::sync::Arc;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
    /// // ... parse database, perform unification ...
    ///
    /// let builder = ProofBuilder::new(db);
    /// // let proof = builder.build_proof(&"ax-1".parse()?, &substitution)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn build_proof(
        &self,
        assertion_label: &Label,
        substitution: &DbSubstitution,
    ) -> Result<Proof, ProofBuildError> {
        todo!("Convert substitution to label sequence")
    }

    /// Build an expanded proof from statement application.
    ///
    /// When `Statement::apply()` succeeds with a substitution, this generates
    /// the corresponding Metamath proof.
    ///
    /// # Arguments
    ///
    /// * `major_label` - The statement being applied to
    /// * `minor_label` - The statement being applied
    /// * `substitution` - The resulting substitution
    ///
    /// # Returns
    ///
    /// An expanded proof showing the application.
    pub fn build_application_proof(
        &self,
        major_label: &Label,
        minor_label: &Label,
        substitution: &DbSubstitution,
    ) -> Result<Proof, ProofBuildError> {
        todo!("Build proof for APPLY operation")
    }

    /// Build an expanded proof from condensed detachment.
    ///
    /// When `Statement::condensed_detach()` succeeds, this generates
    /// the corresponding Metamath proof.
    pub fn build_condensed_detachment_proof(
        &self,
        major_label: &Label,
        minor_label: &Label,
        substitution: &DbSubstitution,
    ) -> Result<Proof, ProofBuildError> {
        todo!("Build proof for CONDENSED_DETACH operation")
    }
}
```

### 4. Parsing Metamath Expressions to DbTerm

Add to `src/metamath/symbolic.rs`:

```rust
/// Parse a Metamath statement (vector of symbols) into a `DbTerm`.
///
/// # Metamath Expression Format
///
/// Metamath expressions are sequences like:
/// - `["wff", "ph"]` - a variable
/// - `["wff", "(", "ph", "->", "ps", ")"]` - implication
/// - `["|-", "(", "ph", "->", "ps", ")"]` - assertion of implication
///
/// # Parsing Strategy
///
/// 1. First symbol is the type code (e.g., `"wff"`, `"|-"`)
/// 2. Remaining symbols are the expression
/// 3. Variables: symbols registered in database via `$f` statements
/// 4. Nodes: constant symbols with syntax axioms defining arity
/// 5. Structure: Prefix notation (Polish notation for operators)
///
/// # Arguments
///
/// * `symbols` - The symbol sequence from Metamath
/// * `db_arc` - Database reference for variable/constant lookups
///
/// # Returns
///
/// A `DbTerm` representing the expression.
///
/// # Errors
///
/// Returns `MguError` if:
/// - Empty symbol vector
/// - Type code not recognized
/// - Unknown symbol (not a variable or constant)
/// - Malformed expression (wrong arity, unmatched parens, etc.)
///
/// # Example
///
/// ```no_run
/// use symbolic_mgu::metamath::{MetamathDatabase, TypeMapping};
/// use symbolic_mgu::metamath::symbolic::parse_expression;
/// use std::sync::Arc;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));
/// // ... register variables and constants ...
///
/// let symbols = vec![
///     Arc::from("wff"),
///     Arc::from("("),
///     Arc::from("ph"),
///     Arc::from("->"),
///     Arc::from("ps"),
///     Arc::from(")")
/// ];
///
/// let term = parse_expression(&symbols, &db)?;
/// # Ok(())
/// # }
/// ```
pub fn parse_expression(
    symbols: &[Arc<str>],
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError> {
    todo!("Parse Metamath expression to DbTerm")
}

/// Helper: parse a single symbol to DbTerm (variable or constant).
fn parse_symbol(
    symbol: &str,
    type_code: &str,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError> {
    todo!("Check if variable (from db.is_variable), else treat as Node")
}

/// Helper: determine if a symbol is a structural constant (paren, operator).
fn is_structural_symbol(symbol: &str) -> bool {
    matches!(symbol, "(" | ")" | "->" | "\\/" | "/\\" | "-." | "=")
}
```

## Phase 1 Detailed Architecture

### Symbol Classification

```rust
/// Symbol kind (constant vs variable)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    Constant,  // Declared with $c
    Variable,  // Declared with $v
}

impl MetamathDatabase {
    /// Symbol kind registry
    symbol_kinds: RwLock<HashMap<Arc<str>, SymbolKind>>,

    pub fn register_constant_symbol(&self, symbol: Arc<str>) -> Result<(), DatabaseError>;
    pub fn register_variable_symbol(&self, symbol: Arc<str>) -> Result<(), DatabaseError>;
    pub fn symbol_kind(&self, symbol: &str) -> Option<SymbolKind>;
    pub fn is_constant(&self, symbol: &str) -> bool;
    pub fn is_variable(&self, symbol: &str) -> bool;
}
```

### Floating Hypothesis Indexing (Scope-Based)

```rust
impl Scope {
    /// Fast lookup: (type_code, variable_name) → FloatingHyp
    floating_hyp_index: HashMap<(Arc<str>, Arc<str>), FloatingHyp>,

    /// Build index inheriting from parent
    fn build_floating_hyp_index(&mut self);

    /// Look up in this scope's index (O(1), already includes parents)
    pub fn lookup_floating_hyp(&self, type_code: &str, variable_name: &str) -> Option<&FloatingHyp>;
}
```

### Syntax Axiom Pattern Index

```rust
/// Preprocessed pattern for efficient matching
#[derive(Debug, Clone)]
pub struct SyntaxAxiomPattern {
    pub label: Label,
    pub type_code: Arc<str>,
    pub pattern: Vec<PatternElement>,
    pub hints: PatternHints,
}

#[derive(Debug, Clone)]
pub enum PatternElement {
    Constant(Arc<str>),
    Variable { name: Arc<str>, type_code: Arc<str> },
}

/// Precomputed hints for fast elimination
#[derive(Debug, Clone)]
pub struct PatternHints {
    pub first_constant: Option<Arc<str>>,
    pub last_constant: Option<Arc<str>>,
    pub constants_in_order: Vec<Arc<str>>,
    pub adjacent_constants: Vec<(Arc<str>, Arc<str>)>,
    pub arity: usize,
}

impl MetamathDatabase {
    /// Syntax axioms indexed by result type
    syntax_axioms_by_type: RwLock<HashMap<Arc<str>, Vec<SyntaxAxiomPattern>>>,

    pub fn get_syntax_axioms_for_type(&self, type_code: &str) -> Vec<SyntaxAxiomPattern>;
    pub fn index_syntax_axiom(&self, axiom: &Axiom);
}
```

### Pattern Matching Algorithm

```rust
/// Main entry point
pub fn parse_expression(
    symbols: &[Arc<str>],
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError>;

/// Recursive parser
fn parse_sequence(
    sequence: &[Arc<str>],
    type_code: &Arc<str>,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError>;

/// Fast pattern elimination
fn filter_patterns(
    sequence: &[Arc<str>],
    candidates: &[SyntaxAxiomPattern],
) -> Result<Vec<SyntaxAxiomPattern>, MguError>;

/// Match sequence against pattern, extract variable subsequences
fn extract_variables(
    sequence: &[Arc<str>],
    pattern: &[PatternElement],
) -> Result<Vec<(Arc<str>, Vec<Arc<str>>)>, MguError>;

/// Parse using matched pattern
fn parse_with_pattern(
    sequence: &[Arc<str>],
    pattern: &SyntaxAxiomPattern,
    db_arc: &Arc<MetamathDatabase>,
) -> Result<DbTerm, MguError>;
```

### Parsing Strategy

1. **Extract type and sequence**: `["wff", "(", "ph", "->", "ps", ")"]` → type="wff", seq=["(", "ph", "->", "ps", ")"]
2. **Check for direct variable**: If single symbol, lookup in floating_hyp_index
3. **Pattern matching**:
   - Get syntax axioms for type
   - Filter by structural hints (first/last constant, constant order, adjacency)
   - If multiple matches, use first (with warning per `nuniq-gram.mm`)
   - Extract variable subsequences from matched pattern
   - Recursively parse each variable's subsequence
4. **Build term**: Create `DbNode` and `DbTerm` with parsed children

## Implementation Phases

### Phase 1: Basic Term Parsing ✅ COMPLETE

**Goal**: Parse Metamath expressions to `DbTerm`

**Status**: Fully implemented in `src/metamath/expr_parser.rs`

**Completed Tasks**:
1. ✅ Implemented `parse_expression()` and `parse_sequence()`
2. ✅ Handle variables (lookup in database via floating hypothesis index)
3. ✅ Handle nodes (syntax axiom constants with pattern matching)
4. ✅ Handle structural symbols (parens, operators)
5. ✅ Type checking during parse

**Deliverable**: ✅ Can convert Metamath statement vectors to `DbTerm` instances

**Tests**: ✅ `tests/metamath_expression_parsing.rs` (10 tests)
- Parse simple variables: `["wff", "ph"]` → `Var(DbMetavariable)`
- Parse simple nodes: `["wff", "(", "ph", "->", "ps", ")"]` → `Node(wi, [ph, ps])`
- Parse nested: `["wff", "(", "(", "ph", "->", "ps", ")", "->", "ch", ")"]`
- Error cases: empty vector, unknown symbol, type mismatch

### Phase 2: AssertionCore to Statement ✅ COMPLETE

**Goal**: Create `Statement` from `AssertionCore`

**Status**: Fully implemented in `src/metamath/database.rs`

**Completed Tasks**:
1. ✅ Implemented `AssertionCore::to_statement()`
2. ✅ Parse assertion to `DbTerm`
3. ✅ Parse hypotheses to `Vec<DbTerm>`
4. ✅ Convert distinctness constraints to `DistinctnessGraph<DbMetavariable>`
5. ✅ Validate types (all Boolean)

**Deliverable**: ✅ Can create `Statement` objects from Metamath axioms/theorems

**Tests**: ✅ `tests/metamath_statement_conversion.rs` (6 tests)
- Convert ax-1 (no essential hypotheses)
- Convert ax-mp (has essential hypotheses)
- Convert theorem with distinctness constraints
- Error: non-Boolean assertion
- Error: malformed expression

### Phase 3: Basic Proof Building ✅ COMPLETE

**Goal**: Generate expanded proofs from substitutions

**Status**: Implemented in `src/metamath/proof_builder.rs` with one known limitation

**Completed Tasks**:
1. ✅ Implemented `ProofBuilder::build_proof()`
2. ✅ Map substitution variables to floating hypothesis labels
3. ✅ Generate label sequence
4. ⚠️ Essential hypotheses: Acknowledged but deferred (requires recursive proof search)

**Deliverable**: ✅ Can generate proof from simple substitution

**Tests**: ✅ `tests/metamath_proof_building.rs` (7 tests)
- Identity substitution → proof with just floating hyps + assertion
- Non-trivial substitution → proof with variable instantiations
- Error handling for missing assertions and hypotheses

**Known Limitation**: Essential hypotheses that require other proofs are not handled. This requires recursive proof search (theorem prover capabilities). See `src/metamath/proof_builder.rs:196-218` for details.

### Phase 4: Advanced Proof Building ✅ COMPLETE

**Goal**: Support APPLY and CONDENSED_DETACH proof generation

**Status**: Fully implemented in `src/metamath/proof_builder.rs`

**Completed Tasks**:
1. ✅ Implemented `ProofBuilder::build_application_proof()`
2. ✅ Implemented `ProofBuilder::build_condensed_detachment_proof()`
3. ✅ Handle complex substitutions
4. ❌ Optimize proof length (not implemented - not critical for correctness)

**Deliverable**: ✅ Full proof generation for all Statement operations

**Tests**: ✅ Included in `tests/metamath_proof_building.rs`
- APPLY proof generation
- CONDENSED_DETACH proof generation
- Multiple axioms and substitutions

**Note**: Both APPLY and CONDENSED_DETACH correctly use modus ponens (ax-mp) as the inference rule.

### Phase 5: Compressed Proof Generation ⏳ DEFERRED (OPTIONAL)

**Goal**: Generate compressed Metamath proofs

**Status**: Not implemented - explicitly marked as future optional work

**Reason**: Expanded proofs are sufficient for correctness. Compression is an optimization that can be added later without breaking changes.

**Future Tasks**:
1. ⏳ Implement proof compression algorithm
2. ⏳ Generate mandatory hypothesis lists
3. ⏳ Generate compressed proof strings
4. ⏳ Validate against verifier

**Future Tests**:
- Round-trip: expand → compress → expand
- Validate compressed proofs verify correctly

## DbNode Implementation

**Status**: ✅ Fully Implemented

`DbNode` is fully implemented in `src/metamath/symbolic.rs`. Key implementation details:

**Structure**:
```rust
pub struct DbNode {
    label: Arc<str>,                    // Syntax axiom label (e.g., "wi")
    database: Arc<MetamathDatabase>,    // Reference for lookups
}
```

**Key Methods** (all implemented):
- `new(label, database)` - Create from syntax axiom label
- `label()` - Get the syntax axiom label
- `database()` - Get database reference

**Node Trait Implementation**:
- `get_arity()` - Looks up arity from syntax axiom pattern
- `get_type(slot)` - Returns type for given child slot
- `try_from_name()` - Panics (requires database context)
- `as_bool_simple_op()` - Maps common operators to `BooleanSimpleOp` (e.g., "wi" → Implication)

**Design Choice**: Uses syntax axiom labels directly (Option A)
- Stores label (e.g., `"wi"`, `"wo"`) as node identifier
- Looks up arity/types from database on demand
- Consistent with how Metamath proofs reference axioms
- Simple, direct mapping without ambiguity

## Key Design Decisions

### 1. Term Representation: EnumTerm vs Wrapper

**Decision**: Use `pub type DbTerm = EnumTerm<DbType, DbMetavariable, DbNode>`

**Rationale**:
- Type parameters already carry `Arc<MetamathDatabase>` references
- No need for additional wrapper layer
- Cleaner type signatures
- Reuses well-tested `EnumTerm` implementation

### 2. Proof Format: Expanded First

**Decision**: Implement expanded proofs, defer compressed proofs

**Rationale**:
- Expanded proofs are simpler (just label sequences)
- Compression is optimization, not correctness requirement
- User explicitly requested this priority
- Can add compression later without breaking changes

### 3. Assertion Scope: Both Axioms and Theorems

**Decision**: Support both via `AssertionCore`

**Rationale**:
- `AssertionCore` contains all needed data (shared by `Axiom` and `Theorem`)
- Assertions with type codes (e.g., `"|-"`) are perfect unification targets
- No reason to artificially restrict to just one

### 4. Novel Discovery Priority

**Decision**: Focus on finding new substitutions, not reproducing existing proofs

**Rationale**:
- Goal: Discover relationships between assertions via unification
- More general substitutions are valuable (shorter proofs)
- Not trying to replicate Metamath's proof verification
- Unification can find substitutions never recorded in proofs

### 5. Type Code Handling

**Decision**: First symbol in Metamath expression is type code, rest is term

**Example**:
```
["|-", "(", "ph", "->", "ps", ")"]
 ^^^    ^^^^^^^^^^^^^^^^^^^^^^^^
 type   term expression
```

**Rationale**:
- Matches Metamath format exactly
- Type code determines term's type
- Enables type checking during parse

## Error Handling Strategy

Following project's `Result` over panicking preference:

**Parsing Errors** (`MguError`):
- Unknown symbol (not variable or constant)
- Malformed expression (wrong arity, structure)
- Type mismatch (non-Boolean in assertion position)
- Empty symbol vector

**Proof Building Errors** (`ProofBuildError`):
- Variable not in database
- Term cannot be represented in Metamath format
- Missing required hypothesis

**Database Errors** (`DatabaseError`):
- Axiom not found
- Syntax axiom has no arity info
- Invalid slot index for node

## Testing Strategy

Following `docs/TESTING_PHILOSOPHY.md`:

### Unit Tests

**Term Parsing**:
- Variables, nodes, compound expressions
- Error cases (malformed, unknown symbols)
- Type checking

**Statement Conversion**:
- Simple axioms (no hypotheses)
- Axioms with hypotheses
- Theorems with distinctness
- Error cases

**Proof Building** (Phase 3+):
- Identity substitution
- Non-trivial substitution
- Multiple hypotheses
- Compressed format (Phase 5)

### Integration Tests

**Real Metamath Assertions**:
- Parse ax-1, ax-2, ax-3 from set.mm
- Convert to Statement
- Perform unification between axioms
- Generate proofs

**PM Corpus Validation**:
- Existing PM proofs continue to work
- Can convert PM theorems to Metamath format

### Property-Based Tests

**Parsing Round-Trip**:
- `statement → DbTerm → statement` preserves meaning
- `DbTerm → symbols → DbTerm` is identity

**Type Safety**:
- Parsed terms always have correct types
- Statements always have Boolean assertions

## Resolved Design Questions

1. **Symbol Classification**: Use `HashMap<Arc<str>, SymbolKind>` registry
   - Symbols declared as constant ($c) or variable ($v) before type binding
   - Mutually exclusive - error to specify same symbol as both
   - Built during database parsing ($c and $v statements)

2. **Floating Hypothesis Indexing**: Scope-based with inheritance
   - Each `Scope` has its own `floating_hyp_index: HashMap<(Arc<str>, Arc<str>), FloatingHyp>`
   - Index built when scope created, inheriting parent's entries
   - Fast lookup: `O(1)` in current scope, no need to traverse chain

3. **Pattern Ambiguity**: Accept first match, log warning if multiple
   - Per `nuniq-gram.mm`: Multiple matches allowed if they derive same syntax theorem
   - When type is specified (our case), should be unambiguous in practice
   - Graceful handling: use first match, warn if ambiguous

4. **Caching**: Deferred to future optimization
   - Originally planned: Cache parsed terms in `AssertionCore` (lazily initialized)
   - Reason for deferral: Not critical for correctness, can be added as performance optimization
   - Future enhancement: Use `OnceLock<DbTerm>` to amortize parsing cost over 40,000+ theorems

## Future Enhancements

The following features were identified but deferred as non-critical optimizations or complex features requiring theorem prover capabilities:

### 1. Term Caching with OnceLock
**Status**: Deferred (performance optimization)

**Description**: Cache parsed `DbTerm` in `AssertionCore` using `OnceLock` pattern to avoid repeated parsing of the same assertion.

**Benefits**:
- Amortizes parsing cost for large databases (40,000+ theorems in set.mm)
- Reduces memory allocations for frequently accessed assertions

**Implementation Sketch**:
```rust
pub struct AssertionCore {
    // ... existing fields ...
    cached_assertion_term: OnceLock<DbTerm>,
}
```

**Effort**: Low - straightforward use of `OnceLock`
**Impact**: Medium - noticeable performance improvement for large databases

### 2. Essential Hypotheses with Recursive Proof Search
**Status**: Deferred (requires theorem prover)

**Description**: Handle essential hypotheses that require other proofs in `ProofBuilder::build_proof()`.

**Current Limitation**: See `src/metamath/proof_builder.rs:196-218`. Assertions with essential hypotheses that require proofs are acknowledged but not handled.

**What's Needed**:
1. Proof search to find which theorems/axioms prove each essential hypothesis
2. Recursive proof building for those dependencies
3. Combine sub-proofs into complete proof

**Complexity**: High - requires automated theorem prover capabilities
**Impact**: High - would enable proof generation for all assertions, not just those with simple hypotheses

### 3. Proof Length Optimization
**Status**: Deferred (optimization)

**Description**: Minimize generated proof length by finding shortest proof sequences.

**Current State**: Generated proofs are correct but may be longer than necessary.

**What's Needed**:
- Proof search to find shorter alternatives
- Heuristics for proof minimization
- Trade-offs between proof search time and proof length

**Complexity**: Medium-High - requires search algorithms
**Impact**: Low - proofs work correctly without this

### 4. Convenience Type Aliases
**Status**: Not implemented (low priority)

**Missing Aliases**:
```rust
pub type DbTermFactory = EnumTermFactory<DbType, DbMetavariable, DbNode>;
pub type DbStatement = Statement<DbType, DbMetavariable, DbNode, DbTerm>;
pub type DbSubstitution = Substitution<DbMetavariable, DbTerm>;
```

**Current State**: Using full type names (e.g., `Substitution<DbMetavariable, DbTerm>`)

**Benefits**: Shorter, more readable type signatures

**Effort**: Trivial - just add type aliases
**Impact**: Low - convenience only, no functionality change

### 5. Compressed Proof Generation (Phase 5)
**Status**: Deferred (explicitly optional)

**Description**: Generate compressed Metamath proof format (not just expanded format).

**What's Needed**:
1. Proof compression algorithm
2. Mandatory hypothesis list generation
3. Compressed proof string generation (Z-stack operations)
4. Validation against Metamath verifier

**Benefits**:
- More compact proof representation
- Matches set.mm standard format

**Complexity**: Medium - compression algorithm is well-defined but non-trivial
**Impact**: Low - expanded proofs are sufficient for correctness

**Note**: Can be added later without breaking changes to existing API.

## Success Criteria

**Phase 1 (Term Parsing)**:
- ✅ Can parse any valid Metamath expression to `DbTerm`
- ✅ Type checking works correctly
- ✅ Error messages are clear and actionable

**Phase 2 (Statement Conversion)**:
- ✅ Can convert any `AssertionCore` to `DbStatement`
- ✅ Hypotheses and distinctness preserved correctly
- ✅ All set.mm axioms parse without error

**Phase 3 (Proof Building)**:
- ✅ Can generate expanded proof from substitution
- ✅ Generated proofs verify correctly in Metamath
- ✅ Works for novel substitutions not in original database

**Phase 4 (Advanced Operations)**:
- ✅ APPLY, CONDENSED_DETACH generate correct proofs
- ✅ Complex substitutions handled properly

## Next Steps

### Completed
1. ✅ **Review this document** - User feedback received and design approved
2. ✅ **Implement Phase 1** - Term parsing infrastructure complete
3. ✅ **Implement Phase 2** - Statement conversion complete
4. ✅ **Implement Phase 3** - Basic proof building complete
5. ✅ **Implement Phase 4** - Advanced proof building complete
6. ✅ **Test implementation** - 23 integration tests, all passing
7. ✅ **Quality gates** - All checks passing (test, clippy, doc, fmt)

### Potential Future Work
See "Future Enhancements" section above for details:

1. **Term Caching** - Performance optimization using `OnceLock`
2. **Essential Hypotheses** - Requires theorem prover capabilities
3. **Proof Optimization** - Minimize proof length
4. **Type Aliases** - Convenience improvements
5. **Compressed Proofs** - Phase 5 (optional)

### Documentation Improvements
1. **Usage Examples** - Create examples showing typical workflows:
   - Parsing Metamath database and creating statements
   - Performing unification between assertions
   - Generating proofs from discovered substitutions
2. **Tutorial** - Step-by-step guide for using the Metamath integration
3. **Performance Analysis** - Document performance characteristics with large databases

## Related Documents

- `docs/METAMATH_ARCHITECTURE_V2.md` - Overall Metamath integration architecture
- `docs/TESTING_PHILOSOPHY.md` - Testing approach and quality gates
- `src/metamath/mod.rs` - Metamath module structure
- `src/statement/mod.rs` - Statement operations

## References

- Megill & Wheeler (2019). *Metamath: A Computer Language for Mathematical Proofs*
- set.mm database - Reference implementation
- Metamath specification - http://us.metamath.org
