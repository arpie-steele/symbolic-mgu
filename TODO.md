# symbolic-mgu TODO List

## Current Priority: Fix bool_eval_next Module

### Context
The `bool_eval_next` module (451 lines in `src/bool_eval_next/mod.rs`) doesn't compile due to:
- Missing `EnumTerm` type (referenced but not implemented)
- Empty `NodeBytes` enum stub (no variants to match)
- Hard-coded dependencies on concrete types instead of trait abstractions

### Architectural Goals
1. **Trait abstractions over concrete types**: Move away from `NodeBytes` and `EnumTerm` concrete types
2. **Factory pattern for construction**: Separate construction (factories) from behavior (traits) (Coded!)
3. **Math correctness first**: Get evaluation logic working and tested
4. **Support 10+ Boolean variables**: Required for condensed detachment test cases

---

## Phase 0: Document Factory Pattern Use

**Type System Examples**:

1. **Default (Metamath/Condensed Detachment)**:
   - `Boolean` - Boolean-valued terms (standalone)
   - `Setvar` - Set-valued variables (subtype of Class)
   - `Class` - Class-valued terms

2. **Extended Mathematics**:
   ```
   Class
   ├─ Setvar
   ├─ OrdinalClass
   ├─ ComplexNumberClass
   ├─ RealNumberClass
   └─ SurrealNumberClass
   ```
   Reasoning about these subtypes reduces needed hypotheses on bare class variables.

3. **Untyped Systems** (e.g., some condensed detachment):
   - Single type, all terms compatible (SimpleBooleanType)
   - `is_subtype_of` always returns true

4. **Other Domains**:
   - Category theory: Objects, Morphisms, Functors
   - Lattice theory: custom type hierarchies
   - Can ignore Boolean/Setvar/Class if not needed

---

### Action Items

#### Documentation
- [ ] Document factory pattern rationale in module-level docs
- [ ] Provide examples of stateful vs. stateless factory implementations
- [ ] Document how factories enable different construction strategies
- [ ] Add examples showing factory usage for different backends (testing, production, database)

#### Design Considerations for Later
- [ ] Consider `StatementFactory` trait (Statements are serialized for long-term storage)
- [ ] Consider factory trait for substitutions/unifications
- [ ] Plan for Rc/Arc integration in concrete factory implementations
- [ ] Design caching strategy for term deduplication

---

## Phase 1: UnsignedBits Implementations

### Special Cases
- `<bool; 0>`: Single bit, already implemented
- `<BigUint; N>`: Arbitrary N, no native `Not` support - special case handling needed

### Generic uXXX Pattern (Macro Candidate)
The pattern `<uXXX; N>` for unsigned integer types should be generalized via macro:
- `<u8; 0..=3>`: 1, 2, 4, 8 bits (0-3 variables)
- `<u16; 0..=4>`: 1, 2, 4, 8, 16 bits (0-4 variables)
- `<u32; 0..=5>`: 1, 2, 4, 8, 16, 32 bits (0-5 variables)
- `<u64; 0..=6>`: 1, 2, 4, 8, 16, 32, 64 bits (0-6 variables)
- `<u128; 0..=7>`: 1, 2, 4, 8, 16, 32, 64, 128 bits (0-7 variables) **[MISSING]**

**Action Items**:
- [ ] Add `<u128; 0..=7>` implementation (supports 7 Boolean variables natively)
- [ ] Design macro to reduce code duplication for `<uXXX; N>` pattern
  - **Decision**: Explicitly call out each `(type, N)` pair - no math in macros to keep them readable
  - Example: `impl_unsigned_bits!(u128, 0); impl_unsigned_bits!(u128, 1); ... impl_unsigned_bits!(u128, 7);`
- [ ] Verify native bitwise ops (`BitAnd`, `BitOr`, `BitXor`, `Not`) work correctly
- [ ] Write unit tests for each implementation (truth table verification)

---

## Phase 2: BooleanNode Trait Abstraction

### Design
Replace hard-coded `NodeBytes` enum matching with trait-based dispatch:

```rust
/// Trait for Boolean logic nodes that can be evaluated
pub trait BooleanNode {
    /// Returns (code, arity) for this Boolean operation, or None if not evaluable
    /// - code: u8 value from NodeBytesLogicTable.md (0x00-0xFF for nullary/unary/binary)
    /// - arity: 0 (nullary), 1 (unary), 2 (binary), 3 (ternary)
    fn boolean_code_arity(&self) -> Option<(u8, usize)>;
}
```

### Rationale
- Decouples evaluation logic from specific node representations
- Allows future serializable database-backed nodes
- Maps 222 human-important operation names to (code, arity) tuples

**Action Items**:
- [ ] Define `BooleanNode` trait in `src/node/boolean.rs`
  - **Decision**: Place in node module since nodes represent more than just Boolean operations
  - Create file if it doesn't exist, add to `src/node/mod.rs` exports
- [ ] Refactor `eval_boolean_node` to accept `<N: BooleanNode>` generic parameter
- [ ] Pattern match on `(u8, arity)` tuples instead of `NodeBytes::*` variants
- [ ] Document mapping from NodeBytesLogicTable.md codes to evaluation behavior

---

## Phase 3: NewTerm Trait Abstraction

### Context
- Previous `Term` trait (in `src/term/base.rs`) exists but is not functional enough
- `EnumTerm<V, NodeBytes>` concrete type was easier to work with (had `MetaLeaf`, `NodeHead` variants)
- Need trait-based abstraction for `bool_eval_next` that doesn't couple to concrete types

### Design Goals
Create `NewTerm` trait (temporary name for bool_eval_next module):
- Support term traversal (distinguish metavariable leaves from node heads)
- Access child terms recursively
- Query node type (via `BooleanNode` trait bound)
- **Note**: This is a prototype; will integrate with main `Term` trait later

### Open Questions
- What methods does `NewTerm` need for evaluation?
  - `is_metavariable(&self) -> bool`?
  - `as_metavariable(&self) -> Option<&V>`?
  - `as_node(&self) -> Option<(&N, &[Self])>` where `N: BooleanNode`?
- Should we use visitor pattern instead of direct trait methods?
- How to handle the generic metavariable type `V`?

**Action Items**:
- [ ] Design `NewTerm` trait with minimal sufficient interface for evaluation
  - **Decision**: Define in `src/bool_eval_next/mod.rs` as temporary prototype
  - Will integrate with main `Term` trait later once design is validated
- [ ] Refactor `eval_boolean_term` to use `NewTerm` instead of `EnumTerm<V, NodeBytes>`
- [ ] Consider: Should `NewTerm` be generic over both `V` (metavariable) and `N` (node)?
- [ ] Write documentation explaining relationship to future unified `Term` trait

---

## Phase 4: Integration and Testing

### Compilation
- [ ] Fix all import errors in `src/bool_eval_next/mod.rs`
- [ ] Resolve `num-bigint` dependency issues (feature gating)
- [ ] Ensure `cargo +1.77 build --all-features` succeeds

### Testing Strategy (Math Correctness First!)
- [ ] Unit tests for `UnsignedBits` trait implementations
  - Verify `mask()`, `n_bits()`, `from_bool()`, `set_bit()` for each type
  - Test bitwise operations match truth tables
- [ ] Integration tests for Boolean evaluation
  - Simple expressions: `Not(True)`, `And(True, False)`, etc.
  - Tautologies: `Or(A, Not(A))` should always evaluate to True
  - 7-variable expressions using `u128` backend
  - 10-variable expressions using `BigUint` backend (with `bigint` feature)
- [ ] Regression tests against previous NodeBytes implementation (if available)

### Code Quality Gates
- [ ] `cargo +1.77 clippy --all-features --all-targets`
- [ ] `cargo +1.77 doc --all-features`
- [ ] `cargo +1.77 test --all-features`

---

## Future Work (Post bool_eval_next)

### Term Trait Unification
- Merge `NewTerm` design lessons into main `Term` trait
- Ensure single unified trait works for all use cases
- Remove temporary `NewTerm` abstraction

### Statement Trait-Based Redesign
- Currently `Statement` is a concrete struct
- May need trait-based approach for Rust-style inheritance

### NodeBytes Implementation
- Implement full `NodeBytes` enum with 222 named operations
- Ensure it implements `BooleanNode` trait
- Maintain backward compatibility with previous design

### Serialization and Database Integration
- Design node representation for serializable theorem databases
- Connect to Metamath and condensed detachment tools
- Trait-based abstraction to support multiple backends

---

## Detailed Design Notes

### Factory Pattern Integration with Evaluation

**Key Insight**: Factories are orthogonal to evaluation logic.

```rust
// CONSTRUCTION PHASE (uses factories)
fn build_test_theorem<NF, MF, TF>(
    node_factory: &NF,
    meta_factory: &MF,
    term_factory: &TF,
) -> Result<impl NewTerm<...>, MguError>
where
    NF: NodeFactory,
    MF: MetavariableFactory,
    TF: TermFactory,
{
    let var_a = meta_factory.create("A", &Type::Boolean)?;
    let var_b = meta_factory.create("B", &Type::Boolean)?;
    let term_a = term_factory.create_leaf(var_a)?;
    let term_b = term_factory.create_leaf(var_b)?;

    let and_node = node_factory.create_by_name("And", 2)?;
    term_factory.create_node(and_node, vec![term_a, term_b])
}

// EVALUATION PHASE (factory-agnostic)
fn evaluate_theorem<V, N, T>(
    term: &T,
    vars: &[V],
) -> Result<u8, MguError>
where
    N: BooleanNode,
    T: NewTerm<V, N>,
{
    // Factory never appears here - only trait interfaces
    u8::eval_boolean_term(term, vars)
}

// USAGE: Different factories, same evaluation
let simple_factory = SimpleNodeFactory::new();
let db_factory = DatabaseNodeFactory::connect("theorems.db")?;

let term1 = build_test_theorem(&simple_factory, ...)?;
let term2 = build_test_theorem(&db_factory, ...)?;

// Same evaluation code works for both
let result1 = evaluate_theorem(&term1, &vars)?;
let result2 = evaluate_theorem(&term2, &vars)?;
```

This separation means:
- **Testing**: Can use simple factories that just construct in-memory objects
- **Production**: Can swap in database/caching factories without touching evaluation code
- **Portability**: Evaluation logic doesn't depend on construction strategy

---

### NewTerm Trait Design Sketch

The key insight from `EnumTerm` was the two-variant pattern:
- `MetaLeaf(V)` - Variable leaf node
- `NodeHead(N, Vec<Self>)` - Operation node with children

Convert this to trait methods:

```rust
// In src/bool_eval_next/mod.rs (temporary location)

/// Trait for terms that can be evaluated as Boolean expressions
/// This is a temporary prototype - will integrate with main Term trait later
pub trait NewTerm<V, N>
where
    V: Clone + Eq,
    N: BooleanNode,
{
    /// Try to extract this term as a metavariable
    fn as_metavariable(&self) -> Option<&V>;

    /// Try to extract this term as a node with children
    /// Returns (node, children_slice) if this is a node head
    fn as_node(&self) -> Option<(&N, &[Self])>;
}
```

**Usage in evaluation**:
```rust
fn eval_boolean_term<V, N, T>(
    term: &T,
    vars: &[V],
) -> Result<Self, MguError>
where
    V: Clone + Eq,
    N: BooleanNode,
    T: NewTerm<V, N>,
{
    // Pattern match on trait methods instead of enum variants
    if let Some(var) = term.as_metavariable() {
        // Handle variable lookup in vars slice
        // ...
    } else if let Some((node, children)) = term.as_node() {
        // Get (code, arity) from BooleanNode trait
        let (code, arity) = node.boolean_code_arity()
            .ok_or_else(|| MguError::unknown_error(695))?;

        // Delegate to eval_boolean_node
        Self::eval_boolean_node(code, arity, children, vars)
    } else {
        Err(MguError::unknown_error(696))
    }
}
```

### BooleanNode Trait Detailed Design

**File**: `src/node/boolean.rs` (new file)

```rust
/// Trait for nodes representing Boolean operations
///
/// This trait allows different node representations to be used
/// with the bool_eval_next evaluation engine by mapping to
/// standardized (code, arity) pairs from NodeBytesLogicTable.md
pub trait BooleanNode {
    /// Returns the Boolean operation code and arity, or None if not evaluable
    ///
    /// # Returns
    /// - `Some((code, arity))` where:
    ///   - `code`: u8 from NodeBytesLogicTable.md (0x00-0xFF)
    ///   - `arity`: 0 (nullary), 1 (unary), 2 (binary), 3 (ternary)
    /// - `None` if this node doesn't represent a Boolean operation
    ///
    /// # Examples
    /// - `True` → `Some((0xFF, 0))`
    /// - `False` → `Some((0x00, 0))`
    /// - `Not` → `Some((0x55, 1))`
    /// - `And` → `Some((0x88, 2))`
    /// - `Or` → `Some((0xEE, 2))`
    fn boolean_code_arity(&self) -> Option<(u8, usize)>;
}
```

**Integration with existing node module**:
```rust
// In src/node/mod.rs
pub mod base;
pub mod enums;
pub mod boolean;  // Add this line

pub use boolean::BooleanNode;  // Re-export for convenience
```

### Evaluation Flow with New Abstractions

**Before (non-compiling)**:
```
eval_boolean_term(&EnumTerm<V, NodeBytes>, ...)
  └─> match term {
        EnumTerm::MetaLeaf(v) => lookup v in vars
        EnumTerm::NodeHead(node, children) =>
          └─> match node {
                NodeBytes::True => ...
                NodeBytes::False => ...
                NodeBytes::And => ...
                // 222 more variants!
              }
      }
```

**After (trait-based)**:
```
eval_boolean_term<V, N, T>(&T, ...) where T: NewTerm<V, N>, N: BooleanNode
  └─> if let Some(v) = term.as_metavariable()
        └─> lookup v in vars
      else if let Some((node, children)) = term.as_node()
        └─> let (code, arity) = node.boolean_code_arity()?
            └─> eval_boolean_node(code, arity, children, vars)
                  └─> match (code, arity) {
                        (0xFF, 0) => handle_true(),
                        (0x00, 0) => handle_false(),
                        (0x55, 1) => handle_not(children),
                        (0x88, 2) => handle_and(children),
                        // Match on (code, arity) tuples instead of enum variants
                      }
```

**Benefits**:
- Evaluation logic decoupled from specific node/term representations
- Can test with minimal stub implementations
- Future node types (database-backed, etc.) just implement traits

### Code Organization After Refactoring

```
src/
├── bool_eval_next/
│   └── mod.rs          # Contains UnsignedBits trait + impls
│                       # Contains NewTerm trait (temporary)
│                       # Contains eval_boolean_* functions
│
├── mgutype/
│   ├── mod.rs          # Module declarations + exports
│   ├── base.rs         # Type enum (Boolean | Setvar | Class) - existing
│   ├── formatting.rs   # Display impls - existing
│   └── trait.rs        # Type trait abstraction (NEW - Phase 0)
│
├── node/
│   ├── mod.rs          # Module declarations + exports
│   ├── base.rs         # Node trait (currently empty stub)
│   ├── enums.rs        # NodeBytes enum (currently empty stub)
│   ├── boolean.rs      # BooleanNode trait (NEW - Phase 2)
│   └── factory.rs      # NodeFactory trait (NEW - Phase 0)
│
├── metavariable/
│   ├── mod.rs          # Module declarations + exports
│   └── factory.rs      # MetavariableFactory trait (NEW - Phase 0)
│
└── term/
    ├── mod.rs          # Module declarations + exports
    ├── base.rs         # Term trait (needs enhancement based on NewTerm lessons)
    └── factory.rs      # TermFactory trait (NEW - Phase 0)
```

---

## Notes

### Macro Design for `<uXXX; N>` Pattern
Current implementations follow consistent pattern:
```rust
impl UnsignedBits<uXXX, N> for uXXX {
    fn mask() -> Self { /* (1 << (1 << N)) - 1 */ }
    fn is_mask_maximum() -> bool { /* N == log2(size_of::<uXXX>() * 8) */ }
    // ... etc
}
```

Candidate macro structure:
```rust
macro_rules! impl_unsigned_bits {
    ($ty:ty, $n:expr) => {
        impl UnsignedBits<$ty, $n> for $ty {
            // Generate standard implementation
        }
    };
}
```

Open questions:
- How to handle const N across macro expansion?
- Should we generate all valid N values for a given type?
- How to ensure type safety (1 << (1 << N) must fit in type)?

### BigUint Special Handling
`BigUint` doesn't have native `Not` trait support - need to implement manually:
- Use `mask XOR value` pattern
- Mask must be computed based on N (number of variables)
- May need custom `Not` implementation or wrapper type

### Practical Examples and Edge Cases

#### Example 1: Simple Tautology - Law of Excluded Middle
**Expression**: `Or(A, Not(A))`

With 1 variable (A):
- Truth table needs 2 bits: `[A=false, A=true]`
- Use `<u8; 1>` (supports up to 2 bits)
- `A` → binary `10` (0b10 = 0x02)
- `Not(A)` → binary `01` (0b01 = 0x01)
- `Or(A, Not(A))` → `11` (0b11 = 0x03) ✓ Always true

#### Example 2: 7-Variable Expression
**Expression**: Complex formula with variables A, B, C, D, E, F, G

- Truth table needs 128 bits (2^7)
- Use `<u128; 7>` (supports exactly 128 bits)
- Each variable maps to pattern:
  - A: `0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA` (alternating)
  - B: `0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC` (pairs)
  - G: `0xFF...00` (128 bits, first 64 set, last 64 unset)

#### Example 3: 10-Variable Condensed Detachment Case
**Expression**: Complex theorem with 10 metavariables

- Truth table needs 1024 bits (2^10)
- Use `<BigUint; 10>` (requires `bigint` feature)
- Pattern generation same, but using arbitrary-precision arithmetic
- Note: `Not` operation implemented as `mask XOR value` where mask = `(1 << 1024) - 1`

#### Edge Case: Arity Mismatch
```rust
// Node says it's binary (arity=2) but has wrong number of children
let node_arity = 2;
let children_len = 3;
if children_len != node_arity {
    return Err(MguError::slots_mismatch(node_arity, children_len));
}
```

#### Edge Case: Unknown Boolean Code
```rust
// Node returns code not in NodeBytesLogicTable.md
match (code, arity) {
    (0xFF, 0) => Self::from_bool(true),  // True
    (0x00, 0) => Self::from_bool(false), // False
    // ... known operations ...
    _ => Err(MguError::unknown_error(697)), // Unknown operation
}
```

#### Edge Case: Variable Not in Binding List
```rust
// Term contains metavariable X, but vars slice is [A, B, C]
if let Some(var) = term.as_metavariable() {
    let index = vars.iter().position(|v| v == var)
        .ok_or_else(|| MguError::unknown_error(698))?;
    // Use index to set corresponding bit...
}
```

### Testing Strategy: Truth Table Verification

For each UnsignedBits implementation, verify against known truth tables:

```rust
#[test]
fn test_not_operation() {
    // For <u8; 1> with 1 variable
    let a = 0b10u8; // Pattern for variable A
    let not_a = !a & u8::mask(); // Apply mask to constrain to 2 bits
    assert_eq!(not_a, 0b01); // Expect inverted pattern
}

#[test]
fn test_and_operation() {
    // For <u8; 2> with 2 variables
    let a = 0b1010u8; // Pattern for variable A
    let b = 0b1100u8; // Pattern for variable B
    let a_and_b = a & b;
    assert_eq!(a_and_b, 0b1000); // Only true when both true
}

#[test]
fn test_tautology_detection() {
    // Or(A, Not(A)) should be all 1s
    let a = 0b10u8;
    let not_a = !a & u8::mask();
    let tautology = a | not_a;
    assert_eq!(tautology, u8::mask()); // Should equal mask (all bits set)
}
```
