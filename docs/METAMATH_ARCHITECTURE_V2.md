# Metamath Database Integration Architecture (Revised)

**Status**: Draft for review
**Date**: 2025-11-15
**Prior version**: METAMATH_ARCHITECTURE.md (replaced by this document)

## Overview

This document outlines the revised design for integrating Metamath database support into symbolic-mgu, incorporating insights from:
- User's pymm Python implementation (~rpenner/projects/pymm)
- metamath-knife difficulties
- Full set.mm scale requirements (222 NodeByte variants already copied from set.mm)
- Need for comment preservation ($t typesetting, $j project hints, datestamps)
- Multiple Metamath type systems (set.mm vs hol.mm)

## Critical Design Revisions

### 1. Type Mapping Must Be Configurable

**Problem**: Different Metamath databases use different type systems.
- set.mm / iset.mm: `wff`, `setvar`, `class`
- hol.mm: `bool` (maps to Boolean), different type hierarchy

**Solution**: Type mappings are **configuration**, not hardcoded in parser.

```rust
/// Configuration for mapping Metamath type codes to our Type system.
#[derive(Debug, Clone)]
pub struct TypeMapping {
    /// Map Metamath type code to our internal type representation.
    boolean_types: HashSet<String>,      // e.g., "wff", "bool"
    setvar_types: HashSet<String>,       // e.g., "setvar"
    class_types: HashSet<String>,        // e.g., "class"
    // Future: custom_types for extensibility
}

impl TypeMapping {
    /// Standard mapping for set.mm and iset.mm.
    pub fn set_mm() -> Self {
        Self {
            boolean_types: ["wff"].iter().map(|s| s.to_string()).collect(),
            setvar_types: ["setvar"].iter().map(|s| s.to_string()).collect(),
            class_types: ["class"].iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Standard mapping for hol.mm.
    pub fn hol_mm() -> Self {
        Self {
            boolean_types: ["bool"].iter().map(|s| s.to_string()).collect(),
            setvar_types: HashSet::new(),
            class_types: HashSet::new(),
        }
    }

    /// Custom mapping for other databases.
    pub fn custom() -> TypeMappingBuilder {
        TypeMappingBuilder::new()
    }
}
```

### 2. Comment Preservation

**Problem**: Significant metadata lives in comments:
- Datestamps: `( Contributed by USER 01-Jan-2020. )`
- Typesetting: `$t` directives for LaTeX/HTML rendering
- Project hints: `$j` directives for proof assistants
- HTML tables and documentation

**Solution**: Parse and preserve comments as structured data.

```rust
/// A comment from the Metamath database.
#[derive(Debug, Clone)]
pub struct Comment {
    /// Raw comment text.
    pub text: String,
    /// Line number where comment starts.
    pub line: usize,
    /// Parsed metadata (if recognized).
    pub metadata: CommentMetadata,
}

#[derive(Debug, Clone, Default)]
pub struct CommentMetadata {
    /// Contribution attribution and date.
    pub contributors: Vec<Contribution>,
    /// Typesetting directives ($t).
    pub typesetting: Option<TypesettingDirective>,
    /// Project-specific hints ($j).
    pub project_hints: Option<ProjectHints>,
    /// HTML tables for documentation.
    pub html_tables: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Contribution {
    pub contributor: String,
    pub date: Option<String>,  // Format: DD-MMM-YYYY
    pub action: ContributionType,  // Contributed, Revised, Proof shortened, etc.
}

/// Statement with associated comments.
#[derive(Debug, Clone)]
pub struct AnnotatedStatement {
    pub label: String,
    pub statement_info: StatementInfo,
    /// Comments immediately preceding this statement.
    pub preceding_comments: Vec<Comment>,
}
```

### 3. Compressed and Expanded Proofs

**Problem**: set.mm uses compressed proofs throughout. Must support both formats.

**Solution**: Parse both, store compressed, expand on demand.

```rust
/// Proof representation supporting both formats.
#[derive(Debug, Clone)]
pub enum Proof {
    /// Expanded proof: sequence of label references.
    Expanded(Vec<String>),
    /// Compressed proof: compact encoding.
    Compressed {
        /// Mandatory hypotheses and prior results.
        labels: Vec<String>,
        /// Compressed proof string.
        proof_string: String,
    },
}

impl Proof {
    /// Expand a compressed proof to label sequence.
    pub fn expand(&self) -> Result<Vec<String>, MetamathError> {
        match self {
            Proof::Expanded(labels) => Ok(labels.clone()),
            Proof::Compressed { labels, proof_string } => {
                expand_compressed_proof(labels, proof_string)
            }
        }
    }

    /// Compress an expanded proof (for optimization).
    pub fn compress(&self, mandatory_count: usize) -> Result<Self, MetamathError> {
        match self {
            Proof::Compressed { .. } => Ok(self.clone()),
            Proof::Expanded(labels) => {
                compress_proof(labels, mandatory_count)
            }
        }
    }
}

/// Expand compressed Metamath proof.
///
/// Compressed proofs use letters A-Z for first 26 references,
/// then AA-ZZ for 27-52, etc. Numbers indicate proof steps.
fn expand_compressed_proof(
    labels: &[String],
    proof_string: &str,
) -> Result<Vec<String>, MetamathError> {
    // Implementation follows Metamath spec section on compressed proofs
    todo!()
}
```

### 4. Scoping Architecture

Inspired by pymm's DatabaseScope parent/child pattern:

```rust
/// Database scope for handling ${ $} blocks.
///
/// Metamath scoping rules:
/// - Constants ($c) are global, declared only in outermost scope
/// - Variables ($v) are scoped but can be redeclared after going inactive
/// - Hypotheses ($f, $e) are scoped
/// - Distinctness ($d) is scoped
/// - Axioms and theorems ($a, $p) are global
struct Scope {
    /// Parent scope (None for outermost).
    parent: Option<Arc<Scope>>,

    /// Variables declared in this scope.
    local_variables: HashMap<String, VariableInfo>,

    /// Floating hypotheses ($f) in this scope.
    floating_hyps: HashMap<String, FloatingHyp>,

    /// Essential hypotheses ($e) in this scope.
    essential_hyps: Vec<EssentialHyp>,

    /// Distinctness constraints in this scope.
    distinctness: Vec<(String, String)>,
}

impl Scope {
    /// Create new child scope.
    fn push_child(&self) -> Scope {
        Scope {
            parent: Some(Arc::new(self.clone())),
            local_variables: HashMap::new(),
            floating_hyps: HashMap::new(),
            essential_hyps: Vec::new(),
            distinctness: Vec::new(),
        }
    }

    /// Look up variable, searching parent scopes.
    fn lookup_variable(&self, name: &str) -> Option<&VariableInfo> {
        self.local_variables.get(name)
            .or_else(|| self.parent.as_ref()?.lookup_variable(name))
    }

    /// Collect all active hypotheses (for building assertions).
    fn collect_hypotheses(&self) -> (Vec<FloatingHyp>, Vec<EssentialHyp>) {
        let mut floating = Vec::new();
        let mut essential = Vec::new();

        let mut current = Some(self);
        while let Some(scope) = current {
            floating.extend(scope.floating_hyps.values().cloned());
            essential.extend(scope.essential_hyps.iter().cloned());
            current = scope.parent.as_ref().map(|arc| arc.as_ref());
        }

        (floating, essential)
    }
}
```

### 5. Full set.mm Scale

**Design for scale from the start**:

```rust
/// Statistics for a loaded database (for debugging/monitoring).
#[derive(Debug, Clone, Default)]
pub struct DatabaseStatistics {
    pub constant_count: usize,
    pub axiom_count: usize,
    pub theorem_count: usize,
    pub total_proof_steps: usize,
    pub max_proof_length: usize,
    pub comment_count: usize,
    pub file_count: usize,  // Includes $[ $] inclusions
}

impl MetamathDatabase {
    /// Load with progress callback for large files.
    pub fn from_file_with_progress<F>(
        path: &Path,
        type_mapping: TypeMapping,
        mut progress: F,
    ) -> Result<Self, MetamathError>
    where
        F: FnMut(usize, &str),  // (line_number, current_label)
    {
        // Parser calls progress() periodically during parse
        todo!()
    }

    /// Get database statistics.
    pub fn statistics(&self) -> DatabaseStatistics {
        todo!()
    }
}
```

**Expected scale for set.mm** (as of 2024):
- ~40,000 theorems
- ~6,000 axioms
- ~15,000 definitions
- Largest proofs >10,000 steps
- 222+ constant symbols (already used in NodeByte)

## Revised Database Architecture

### Core Database Structure

```rust
#[cfg(feature = "metamath")]
pub struct MetamathDatabase {
    /// Type mapping configuration.
    type_mapping: TypeMapping,

    /// Global constants (from $c).
    constants: HashMap<String, ConstantInfo>,

    /// All axioms and theorems (global).
    statements: HashMap<String, AnnotatedStatement>,

    /// Current scope stack (during parsing).
    scopes: Vec<Scope>,

    /// File inclusion tracking ($[ $]).
    included_files: HashSet<PathBuf>,

    /// All comments (preserved for metadata).
    comments: Vec<Comment>,

    /// Statistics.
    stats: DatabaseStatistics,
}

#[derive(Debug, Clone)]
pub struct ConstantInfo {
    pub symbol: String,
    pub line_declared: usize,
    /// Arity determined from usage in $a syntax statements.
    pub arity: Option<usize>,
    /// Type code if this constant is a type symbol.
    pub is_type: bool,
}

#[derive(Debug, Clone)]
pub struct VariableInfo {
    pub symbol: String,
    pub bound_type: Option<String>,  // From $f statement
    pub active: bool,
}

#[derive(Debug, Clone)]
pub struct FloatingHyp {
    pub label: String,
    pub variable: String,
    pub type_code: String,
}

#[derive(Debug, Clone)]
pub struct EssentialHyp {
    pub label: String,
    pub statement: Vec<String>,
}
```

### Parser Architecture

Based on pymm's tokenizer + state machine approach:

```rust
/// Tokenizer for Metamath files.
struct Tokenizer {
    /// Stack of files (for $[ $] inclusion).
    file_stack: Vec<BufReader<File>>,
    /// Already-included files.
    included: HashSet<PathBuf>,
    /// Current line number.
    line: usize,
    /// Token buffer.
    buffer: VecDeque<Token>,
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    value: String,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    // Keywords
    BeginConstant,      // $c
    BeginVariable,      // $v
    BeginFloating,      // $f
    BeginEssential,     // $e
    BeginAxiom,         // $a
    BeginTheorem,       // $p
    BeginDisjoint,      // $d
    BeginScope,         // ${
    EndScope,           // $}
    BeginComment,       // $(
    EndComment,         // $)
    BeginInclusion,     // $[
    EndInclusion,       // $]
    EndStatement,       // $.
    BeginProof,         // $=

    // Content
    Word,               // Label or symbol
    Whitespace,
    Newline,
}

impl Tokenizer {
    fn new(file: File) -> Self {
        Self {
            file_stack: vec![BufReader::new(file)],
            included: HashSet::new(),
            line: 1,
            buffer: VecDeque::new(),
        }
    }

    /// Read next token, handling file inclusion.
    fn next_token(&mut self) -> Result<Option<Token>, MetamathError> {
        todo!()
    }

    /// Skip whitespace and comments (unless preserving comments).
    fn skip_whitespace(&mut self) {
        todo!()
    }

    /// Read comment text (for preservation).
    fn read_comment(&mut self) -> Result<Comment, MetamathError> {
        todo!()
    }

    /// Handle $[ filename $] inclusion.
    fn include_file(&mut self, filename: &str) -> Result<(), MetamathError> {
        todo!()
    }
}

/// Parser state machine.
struct Parser {
    tokenizer: Tokenizer,
    database: MetamathDatabase,
    current_label: Option<String>,
}

impl Parser {
    /// Parse entire database.
    fn parse(&mut self) -> Result<(), MetamathError> {
        while let Some(token) = self.tokenizer.next_token()? {
            match token.kind {
                TokenKind::Word => {
                    self.current_label = Some(token.value);
                }
                TokenKind::BeginConstant => self.parse_constant()?,
                TokenKind::BeginVariable => self.parse_variable()?,
                TokenKind::BeginFloating => self.parse_floating()?,
                TokenKind::BeginEssential => self.parse_essential()?,
                TokenKind::BeginAxiom => self.parse_axiom()?,
                TokenKind::BeginTheorem => self.parse_theorem()?,
                TokenKind::BeginDisjoint => self.parse_disjoint()?,
                TokenKind::BeginScope => self.push_scope(),
                TokenKind::EndScope => self.pop_scope(),
                TokenKind::BeginComment => {
                    let comment = self.tokenizer.read_comment()?;
                    self.database.comments.push(comment);
                }
                _ => return Err(MetamathError::unexpected_token(token)),
            }
        }
        Ok(())
    }

    fn parse_constant(&mut self) -> Result<(), MetamathError> {
        // Read symbols until $.
        todo!()
    }

    fn parse_theorem(&mut self) -> Result<(), MetamathError> {
        // Read statement until $=, then proof until $.
        // Parse both compressed and expanded proofs
        todo!()
    }

    // ... other parse methods
}
```

## SymbolicDatabase Trait (Revised)

```rust
/// Trait for databases that provide symbolic entities.
pub trait SymbolicDatabase: Send + Sync {
    /// Get type mapping for this database.
    fn type_mapping(&self) -> &TypeMapping;

    /// Get a constant by symbol.
    fn get_constant(&self, symbol: &str) -> Option<&ConstantInfo>;

    /// Get a statement by label.
    fn get_statement(&self, label: &str) -> Option<&AnnotatedStatement>;

    /// Get comments associated with a label.
    fn get_comments(&self, label: &str) -> Vec<&Comment>;

    /// Verify a proof.
    fn verify_proof(&self, label: &str) -> Result<bool, MetamathError>;

    /// Get database statistics.
    fn statistics(&self) -> DatabaseStatistics;
}
```

## Database-Backed Implementations (Revised)

```rust
#[cfg(feature = "metamath")]
#[derive(Clone)]
pub struct DbType {
    type_code: String,
    database: Arc<dyn SymbolicDatabase>,
}

impl Type for DbType {
    fn is_boolean(&self) -> bool {
        self.database.type_mapping().boolean_types.contains(&self.type_code)
    }

    fn is_setvar(&self) -> bool {
        self.database.type_mapping().setvar_types.contains(&self.type_code)
    }

    fn is_class(&self) -> bool {
        self.database.type_mapping().class_types.contains(&self.type_code)
    }
}
```

## Error Handling

Following pymm's exception hierarchy:

```rust
#[derive(Debug, thiserror::Error)]
pub enum MetamathError {
    #[error("Symbol already in use: {symbol}")]
    SymbolInUse { symbol: String },

    #[error("Label already in use: {label}")]
    LabelInUse { label: String },

    #[error("Illegal symbol: {symbol}")]
    IllegalSymbol { symbol: String },

    #[error("No such symbol: {symbol}")]
    NoSuchSymbol { symbol: String },

    #[error("No such constant: {symbol}")]
    NoSuchConstant { symbol: String },

    #[error("No such variable: {symbol}")]
    NoSuchVariable { symbol: String },

    #[error("Unexpected token at line {line}: {token:?}")]
    UnexpectedToken { line: usize, token: Token },

    #[error("Proof verification failed for {label}: {reason}")]
    VerificationFailed { label: String, reason: String },

    #[error("Compressed proof expansion failed: {reason}")]
    CompressionError { reason: String },

    #[error("File inclusion failed: {path}: {source}")]
    InclusionError {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("Parse error at line {line}: {message}")]
    ParseError { line: usize, message: String },
}
```

## Testing Strategy (Revised)

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_minimal_database() {
        let mm = r#"
            $c ( ) -> wff $.
            $v ph ps $.
            $( Simp axiom. $)
            ax-1 $a wff ( ph -> ( ps -> ph ) ) $.
        "#;
        let db = MetamathDatabase::from_str(mm, TypeMapping::set_mm()).unwrap();
        assert_eq!(db.statements.len(), 1);
    }

    #[test]
    fn test_compressed_proof() {
        let compressed = Proof::Compressed {
            labels: vec!["ax-1".to_string(), "ax-mp".to_string()],
            proof_string: "ABCD".to_string(),
        };
        let expanded = compressed.expand().unwrap();
        // Verify expansion matches specification
    }

    #[test]
    fn test_comment_metadata() {
        let comment = Comment {
            text: "( Contributed by Norman Megill, 5-Aug-1993. )".to_string(),
            line: 42,
            metadata: Default::default(),
        };
        let parsed = parse_comment_metadata(&comment).unwrap();
        assert_eq!(parsed.contributors.len(), 1);
        assert_eq!(parsed.contributors[0].contributor, "Norman Megill");
    }
}
```

### Integration Tests

```rust
#[test]
#[ignore]  // Large file test
fn test_full_set_mm() {
    let path = Path::new("test_data/set.mm");
    let mut progress_count = 0;
    let db = MetamathDatabase::from_file_with_progress(
        path,
        TypeMapping::set_mm(),
        |line, label| {
            progress_count += 1;
            if progress_count % 1000 == 0 {
                eprintln!("Line {}: {}", line, label);
            }
        },
    ).unwrap();

    eprintln!("Database statistics: {:?}", db.statistics());
    assert!(db.statistics().theorem_count > 30000);
}
```

## Design Decisions (Finalized 2025-11-15)

### 1. Arity Determination
**Decision**: Parse syntax axioms ($a statements) to determine Node arity.

**Implementation**: The syntax axioms give us:
- Node name (the constant being defined)
- Node type (e.g., `wff`, `class`)
- Zero or more symbols previously declared with $c or $v

**The number of $v symbols tells us the arity.**

Example from set.mm:
```metamath
$( Syntax axiom for implication $)
wi $a wff ( ph -> ps ) $.
```
Here: `wi` is the node name, `wff` is the type, and `ph`, `ps` are variables → arity = 2.

### 2. Comment Parsing Depth
**Decision**: Prioritize contributor parsing for academic credit.

**Priority order**:
1. **Contributors** (HIGHEST): Parse contribution attributions for academic credit
   - Format: `( Contributed by NAME, DD-MMM-YYYY. )`
   - This is essential for preserving scholarly attribution
2. **$t directives** (LOWER): Defer until later
   - Can default to ASCII output support for early work
   - Not a priority for initial implementation
3. **$j directives** (LOWER): Less priority
   - Has many different audiences
   - Defer until core functionality working

**Implementation**: Phase 5 focuses on contributor parsing, other metadata deferred.

### 3. Proof Verification Algorithm
**Decision**: Implement stack-based explicit substitution engine (different from APPLY/CONTRACT).

**Rationale**: Metamath proof unpacking uses a stack-based explicit substitution engine that is **subtly different** from our APPLY/CONTRACT operations. The Metamath verifier:
- Unpacks compressed proof strings or label lists
- Uses explicit substitution on a stack
- May allow us to find more general substitutions than those used in a particular proof

**Implementation approach**:
- Separate verifier module following mmverify.py algorithm
- Keep it independent from APPLY/CONTRACT initially
- Future: Explore connection between Metamath substitution and our unification

### 4. Memory vs Speed Tradeoffs
**Decision**: Load proof strings into memory, unpack to structured data on-demand.

**Implementation**:
```rust
pub struct StoredProof {
    /// Proof string stored in memory (compressed or expanded).
    proof_string: Proof,  // enum: Compressed or Expanded

    /// Unpacked structured proof (cached on first access).
    unpacked: OnceLock<StructuredProof>,
}

impl StoredProof {
    /// Unpack proof on-demand, cache result.
    pub fn unpack(&self) -> Result<&StructuredProof, MetamathError> {
        self.unpacked.get_or_try_init(|| {
            unpack_proof(&self.proof_string)
        })
    }
}
```

**Tradeoff**:
- Memory: O(n) for proof strings (unavoidable)
- CPU: First access unpacks, subsequent accesses are O(1)
- Scales well for 40,000 theorems

### 5. Serialization Strategy
**Decision**: Defer serialization until database integration is working.

**Rationale**:
- Focus on getting core functionality correct first
- Serialization with Arc references is complex
- Can revisit once we understand usage patterns

**Future options**:
- DatabaseRegistry pattern (from V1 architecture)
- Store database path + label, reload on deserialize
- Custom serde implementation

## Implementation Phases (Revised)

### Phase 1: Tokenizer and Basic Parser
- Implement Tokenizer with file inclusion
- Basic token recognition
- Test with minimal .mm files
- **Deliverable**: Can tokenize set.mm without errors

### Phase 2: Database Structure and Scoping
- Implement Scope with parent/child
- Implement MetamathDatabase with TypeMapping
- Parse $c, $v, ${, $}
- Test scoping rules
- **Deliverable**: Can parse variables and constants from set.mm

### Phase 3: Statements Without Proofs
- Parse $a, $f, $e, $d
- Build AnnotatedStatement
- Test with set.mm axioms
- **Deliverable**: Can extract all axioms from set.mm

### Phase 4: Proof Parsing
- Parse $p with $= proofs
- Handle both compressed and expanded
- **Deliverable**: Can parse all proofs from set.mm (not verify yet)

### Phase 5: Comment Preservation
- Parse $(  $) comments
- Extract metadata (contributors, dates)
- Associate comments with statements
- **Deliverable**: Can extract comment metadata from set.mm

### Phase 6: Database-Backed Types
- Implement DbType, DbMetavariable, DbNode
- Connect to MetamathDatabase
- Test with simple theorems
- **Deliverable**: Can create Terms from Metamath expressions

### Phase 7: Proof Verification
- Implement proof verifier
- Test with pmproofs examples
- Verify against known correct proofs
- **Deliverable**: Can verify proofs from set.mm

## Dependencies

### Recommended: Implement Our Own Parser

**Pros:**
- Educational value for academic audience
- Full control over error messages and metadata
- No external dependency to maintain
- Demonstrates Metamath format clearly

**Cons:**
- More implementation work
- Need to handle edge cases ourselves

**Decision**: Implement our own parser. The format is well-specified and not overly complex.

### Only External Dependency Needed

```toml
[dependencies]
# Existing dependencies remain unchanged
```

No new dependencies required for basic Metamath support.

Optional future dependencies:
- `regex` (already in dependency tree via other crates)
- Consider lazy_static or once_cell for type mapping singletons (but stdlib OnceLock works for MSRV 1.77)

## Academic and Educational Value

This implementation will demonstrate:

1. **Metamath Format**: Clear, documented parsing of a proven mathematical format
2. **Scoping Semantics**: How mathematical scopes work in practice
3. **Proof Verification**: Mechanical checking of mathematical proofs
4. **Historical Preservation**: Respecting 30+ years of Metamath development
5. **Type System Flexibility**: How different logical systems map to same framework
6. **Scale Handling**: Techniques for parsing and managing large databases

## Alignment with Project Goals

This architecture supports all three novel features:

1. **Historical Notation**: Comments and metadata preserve historical context
2. **Truth Function Exploration**: Metamath provides source of Boolean theorems
3. **Metamath Verifier**: Core goal, fully supported by this design

## Next Steps

After architecture review:

1. Create feature branch: `feature/metamath-integration`
2. Start Phase 1: Tokenizer implementation
3. Create test fixtures from set.mm samples
4. Iterate on design as implementation reveals issues

## References

- Megill & Wheeler (2019). *Metamath: A Computer Language for Mathematical Proofs*
- ~rpenner/projects/pymm - Python reference implementation
- metamath-knife - Rust implementation (consulted but found difficult)
- mmverify.py - Canonical verifier (Raph Levien, 2002)
- set.mm - Main Metamath database
- http://us.metamath.org - Official documentation
