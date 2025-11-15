# Metamath Database Integration Architecture

## Overview

This document outlines the design for integrating Metamath database support into symbolic-mgu. Metamath support will be behind a feature flag and will introduce database-backed implementations of Type, Metavariable, and Node that reference shared database state via Rc/Arc.

## Feature Flag

```toml
[features]
metamath = ["dep:metamath-parser"]  # TBD: exact dependency
```

**Rationale**: Not all users need Metamath support. The feature adds:
- Additional dependencies for parsing .mm files
- Database management overhead
- Complexity for users who only need standalone unification

## Metamath Database Format (Summary)

Based on Metamath specification:

### Statement Types
- `$c ... $.` - Constant declaration (global, cannot be inside ${ $})
- `$v ... $.` - Variable declaration (scoped)
- `$f ... $.` - Floating hypothesis (variable type declaration, scoped)
- `$e ... $.` - Essential hypothesis (logical assumption, scoped)
- `$a ... $.` - Axiom/definition/syntax (global, survives scope)
- `$p ... $= ... $.` - Theorem with proof (global, survives scope)
- `$d ... $.` - Disjoint variable restriction (distinctness, scoped)
- `${ ... $}` - Scoping block

### Key Characteristics
1. **Scoping**: $c, $a, $p are global. Others are scoped by ${ $}.
2. **Distinctness**: $d statements create distinctness constraints (maps to our DistinctnessGraph)
3. **Types**: $f statements assign types to variables (maps to our Type system)
4. **Proofs**: $p statements contain compressed proofs that need verification

## Database Architecture

### Core Database Trait

```rust
/// Trait for databases that provide symbolic entities.
///
/// Implementations hold parsed Metamath databases or other sources
/// of symbolic definitions. Types, Nodes, and Metavariables can
/// reference a database via Rc/Arc for shared access.
pub trait SymbolicDatabase {
    /// Get a constant by its identifier.
    fn get_constant(&self, id: &str) -> Option<ConstantInfo>;

    /// Get a type symbol by its identifier.
    fn get_type_symbol(&self, id: &str) -> Option<TypeInfo>;

    /// Get variable type information.
    fn get_variable_type(&self, var_id: &str) -> Option<TypeInfo>;

    /// Get axiom or theorem by label.
    fn get_statement(&self, label: &str) -> Option<StatementInfo>;

    /// Get all active distinctness constraints in scope.
    fn get_distinctness_constraints(&self, scope: &str) -> Vec<(String, String)>;
}

/// Information about a constant from the database.
#[derive(Debug, Clone)]
pub struct ConstantInfo {
    pub symbol: String,
    pub type_code: String,  // e.g., "wff" for well-formed formula
    pub description: Option<String>,
}

/// Information about a type from the database.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub type_code: String,
    pub description: Option<String>,
}

/// Information about a statement (axiom or theorem) from the database.
#[derive(Debug, Clone)]
pub struct StatementInfo {
    pub label: String,
    pub statement_type: StatementType,  // Axiom or Theorem
    pub hypotheses: Vec<String>,
    pub assertion: String,
    pub proof: Option<Vec<String>>,  // Compressed proof steps
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementType {
    Axiom,
    Theorem,
}
```

### Metamath Database Implementation

```rust
#[cfg(feature = "metamath")]
pub struct MetamathDatabase {
    constants: HashMap<String, ConstantInfo>,
    type_symbols: HashMap<String, TypeInfo>,
    statements: HashMap<String, StatementInfo>,
    scopes: Vec<Scope>,  // Stack of scopes for ${ $} blocks
    distinctness: HashMap<String, Vec<(String, String)>>,
}

#[cfg(feature = "metamath")]
impl MetamathDatabase {
    /// Parse a Metamath database from a .mm file.
    pub fn from_file(path: &Path) -> Result<Self, MetamathError> {
        // Parse .mm file
        // Build internal structures
        // Return database
        todo!()
    }

    /// Parse from a string (for testing).
    pub fn from_str(content: &str) -> Result<Self, MetamathError> {
        todo!()
    }

    /// Verify a proof from the database.
    pub fn verify_proof(&self, label: &str) -> Result<bool, MetamathError> {
        // Use Statement operations to verify proof
        todo!()
    }
}

#[cfg(feature = "metamath")]
impl SymbolicDatabase for MetamathDatabase {
    // Implementation of trait methods
}
```

## Database-Backed Implementations

### Database-Backed Type

```rust
#[cfg(feature = "metamath")]
#[derive(Clone)]
pub struct DbType {
    type_code: String,
    database: Arc<dyn SymbolicDatabase>,
}

#[cfg(feature = "metamath")]
impl DbType {
    pub fn new(type_code: String, database: Arc<dyn SymbolicDatabase>) -> Self {
        Self { type_code, database }
    }
}

#[cfg(feature = "metamath")]
impl Type for DbType {
    fn is_boolean(&self) -> bool {
        self.type_code == "wff"  // well-formed formula
    }

    fn is_setvar(&self) -> bool {
        self.type_code == "setvar"
    }

    fn is_class(&self) -> bool {
        self.type_code == "class"
    }

    // Other Type trait methods...
}

#[cfg(feature = "metamath")]
impl TypeCore for DbType {
    // Core type methods
}
```

### Database-Backed Metavariable

```rust
#[cfg(feature = "metamath")]
#[derive(Clone)]
pub struct DbMetavariable {
    symbol: String,
    type_info: TypeInfo,
    database: Arc<dyn SymbolicDatabase>,
}

#[cfg(feature = "metamath")]
impl DbMetavariable {
    pub fn new(
        symbol: String,
        database: Arc<dyn SymbolicDatabase>
    ) -> Result<Self, MguError> {
        let type_info = database
            .get_variable_type(&symbol)
            .ok_or_else(|| MguError::unknown_variable(&symbol))?;
        Ok(Self { symbol, type_info, database })
    }
}

#[cfg(feature = "metamath")]
impl Metavariable for DbMetavariable {
    type Type = DbType;

    fn get_type(&self) -> Self::Type {
        DbType::new(
            self.type_info.type_code.clone(),
            Arc::clone(&self.database)
        )
    }

    // Other Metavariable trait methods...
}
```

### Database-Backed Node

```rust
#[cfg(feature = "metamath")]
#[derive(Clone)]
pub struct DbNode {
    symbol: String,
    arity: usize,
    type_info: TypeInfo,
    database: Arc<dyn SymbolicDatabase>,
}

#[cfg(feature = "metamath")]
impl DbNode {
    pub fn new(
        symbol: String,
        database: Arc<dyn SymbolicDatabase>
    ) -> Result<Self, MguError> {
        let const_info = database
            .get_constant(&symbol)
            .ok_or_else(|| MguError::unknown_constant(&symbol))?;

        // Determine arity from type signature
        let arity = Self::determine_arity(&const_info)?;

        Ok(Self {
            symbol,
            arity,
            type_info: TypeInfo {
                type_code: const_info.type_code,
                description: const_info.description,
            },
            database,
        })
    }

    fn determine_arity(info: &ConstantInfo) -> Result<usize, MguError> {
        // Parse type signature to determine arity
        // E.g., "( wff wff wff )" means binary operator (2 args)
        todo!()
    }
}

#[cfg(feature = "metamath")]
impl Node for DbNode {
    type Type = DbType;

    fn get_type(&self) -> Self::Type {
        DbType::new(
            self.type_info.type_code.clone(),
            Arc::clone(&self.database)
        )
    }

    fn arity(&self) -> usize {
        self.arity
    }

    // Other Node trait methods...
}
```

## API Changes Needed

### Current API (No Breaking Changes)

The existing API continues to work as-is:
- `EnumTerm`, `MetaByte`, `NodeByte` - standalone implementations
- All current traits remain unchanged
- No breaking changes to existing code

### New API (Feature-Gated)

```rust
#[cfg(feature = "metamath")]
pub mod metamath {
    pub use crate::metamath_db::{
        MetamathDatabase,
        DbType,
        DbMetavariable,
        DbNode,
        SymbolicDatabase,
    };

    pub type DbTerm = /* Term implementation using DbNode/DbMetavariable */;
    pub type DbStatement = /* Statement using DbTerm */;
}
```

### Usage Example

```rust
#[cfg(feature = "metamath")]
{
    use symbolic_mgu::metamath::{MetamathDatabase, DbStatement};

    // Load Metamath database
    let db = MetamathDatabase::from_file("set.mm")?;
    let db = Arc::new(db);

    // Get a theorem
    let theorem = db.get_statement("pm2.43")?;

    // Verify its proof
    db.verify_proof("pm2.43")?;

    // Use in unification
    let term1 = DbTerm::from_metamath_expr(&theorem.assertion, Arc::clone(&db))?;
    let term2 = /* ... */;
    let mgu = unify(&term1, &term2)?;
}
```

## Serialization Strategy

### Challenge

Database-backed types contain Arc references that cannot be directly serialized.

### Solution: Serialization Proxy Pattern

```rust
#[cfg(all(feature = "metamath", feature = "serde"))]
#[derive(Serialize, Deserialize)]
pub struct DbTypeProxy {
    type_code: String,
    database_id: String,  // Identifier for database instance
}

#[cfg(all(feature = "metamath", feature = "serde"))]
impl DbType {
    /// Serialize with database registry.
    pub fn to_proxy(&self, registry: &DatabaseRegistry) -> DbTypeProxy {
        DbTypeProxy {
            type_code: self.type_code.clone(),
            database_id: registry.get_id(&*self.database),
        }
    }

    /// Deserialize with database registry.
    pub fn from_proxy(
        proxy: DbTypeProxy,
        registry: &DatabaseRegistry
    ) -> Result<Self, MguError> {
        let database = registry.get_database(&proxy.database_id)?;
        Ok(Self::new(proxy.type_code, database))
    }
}

/// Registry for managing database instances during serialization.
pub struct DatabaseRegistry {
    databases: HashMap<String, Arc<dyn SymbolicDatabase>>,
}
```

## Module Structure

```
src/
├── lib.rs                          (existing, add metamath feature gate)
├── metamath/                       (NEW, #[cfg(feature = "metamath")])
│   ├── mod.rs                      (public exports)
│   ├── database.rs                 (MetamathDatabase implementation)
│   ├── parser.rs                   (Parse .mm files)
│   ├── db_type.rs                  (DbType implementation)
│   ├── db_metavariable.rs          (DbMetavariable implementation)
│   ├── db_node.rs                  (DbNode implementation)
│   ├── db_term.rs                  (Term implementation)
│   ├── verifier.rs                 (Proof verification)
│   ├── error.rs                    (MetamathError types)
│   └── registry.rs                 (DatabaseRegistry for serialization)
└── ... (existing modules)
```

## Dependencies

### Required for `metamath` Feature

```toml
[dependencies]
# Existing dependencies...

# NEW - only with metamath feature
metamath-parser = { version = "TBD", optional = true }
# OR implement our own parser (preferred for academic/educational value)
```

**Recommendation**: Implement our own parser rather than adding dependency.
- Educational value (show how .mm files work)
- Full control over error messages
- Academic audience appreciates understanding format
- Avoids dependency on external crate

### Parser Implementation Outline

```rust
/// Tokenize a Metamath database file.
fn tokenize(content: &str) -> Vec<Token>;

/// Parse tokens into database structure.
fn parse(tokens: Vec<Token>) -> Result<MetamathDatabase, MetamathError>;

/// Token types in Metamath format.
enum Token {
    Constant,           // $c
    Variable,           // $v
    Floating,           // $f
    Essential,          // $e
    Axiom,              // $a
    Provable,           // $p
    Disjoint,           // $d
    BlockOpen,          // ${
    BlockClose,         // $}
    StatementEnd,       // $.
    ProofStart,         // $=
    Symbol(String),     // Any other token
}
```

## Testing Strategy

### Unit Tests
- Parse minimal .mm databases
- Test database queries
- Test database-backed Type/Metavariable/Node creation
- Test Arc reference counting

### Integration Tests
- Verify proofs from pmproofs history
- Load small Metamath databases (not full set.mm)
- Round-trip serialization with DatabaseRegistry

### Example Test Database

```metamath
$( Minimal test database $)
$c ( ) -> wff $.
$v ph ps $.
$f wff ph $.
$f wff ps $.
ax-1 $a wff ( ph -> ( ps -> ph ) ) $.
${
  min $e wff ph $.
  maj $e wff ( ph -> ps ) $.
  ax-mp $a wff ps $.
$}
```

## Open Questions

1. **Arity determination**: How to determine Node arity from Metamath syntax declarations?
   - Requires parsing type signatures like `( wff wff wff )`
   - May need helper functions in MetamathDatabase

2. **Type equivalence**: How to map Metamath type codes to SimpleType enum?
   - `wff` → Boolean
   - `setvar` → Setvar
   - `class` → Class
   - Others → Custom types via Type trait?

3. **Proof compression**: Metamath uses compressed proof format. Do we:
   - Store compressed and decompress on demand?
   - Decompress during parsing and store expanded?
   - Support both?

4. **Database versioning**: How to handle evolving Metamath databases?
   - Store database format version in file?
   - Version checking during load?

## Implementation Phases

### Phase 1: Core Infrastructure (Recommended First)
1. Define SymbolicDatabase trait
2. Implement basic MetamathDatabase (empty, no parsing)
3. Implement DbType, DbMetavariable, DbNode with trait impls
4. Add feature flag and module structure
5. Write tests with mock database

### Phase 2: Parser
1. Implement tokenizer
2. Implement parser for each statement type
3. Handle scoping (${ $} blocks)
4. Build internal data structures
5. Test with minimal .mm files

### Phase 3: Verifier
1. Implement proof verification logic
2. Use existing Statement operations
3. Handle compressed proof format
4. Test with pmproofs examples

### Phase 4: Serialization (Optional)
1. Implement DatabaseRegistry
2. Add serialization proxies
3. Test round-trip serialization

## Academic Value

This implementation serves multiple educational purposes:

1. **Format Understanding**: Show how Metamath encodes mathematical knowledge
2. **Proof Verification**: Demonstrate mechanical proof checking
3. **Database Design**: Illustrate shared-reference patterns in Rust
4. **Historical Context**: Connect to Megill's work and pmproofs history
5. **Type Systems**: Show how Metamath types map to our Type trait

## References

- Megill, N. and Wheeler, D. A. (2019) *Metamath: A Computer Language for Mathematical Proofs*
- http://us.metamath.org - Metamath project homepage
- http://us.metamath.org/mmsolitaire/mms.html - Metamath Solitaire applet
- set.mm - Main Metamath database (set theory + logic)
- pmproofs history - Condensed detachment examples
