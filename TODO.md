# symbolic-mgu TODO List

## 📊 Overall Progress: 56% Complete

**Summary of staged changes (3,690 additions / 101 deletions across 23 files):**

| Phase | Status | Completion | Critical Gaps |
|-------|--------|------------|---------------|
| Phase 0: Factory Pattern | ⚠️ Partial | 50% | Missing documentation |
| Phase 1: UnsignedBits | ⚠️ Partial | 40% | Missing u16/u32/u64/u128, no tests |
| Phase 2: BooleanNode | ✅ Mostly Done | 75% | BooleanSimpleOp not integrated |
| Phase 3: Term Abstraction | ✅ Complete | 90% | Minor polish possible |
| Phase 4: Testing | ❌ Critical | 20% | **Zero tests added** |

**Critical blockers before merge:**
1. ❌ **Zero tests** - Violates "Math correctness is Job #1"
2. ❌ **Missing u128** - Cannot support 7-variable requirement
3. ⚠️ **Compilation unverified** - Quality gates not run

---

## Current Priority: Fix bool_eval_next Module

### Context (UPDATED)
The `bool_eval_next` module has been significantly expanded (1,509 lines in `src/bool_eval_next/mod.rs`):
- ✅ `EnumTerm` type implemented in `src/term/simple.rs` (150 lines)
- ✅ `NodeByte` enum implemented with 222+ operations in `src/node/node_byte/base.rs` (1,375 lines)
- ✅ `BooleanSimpleOp` enum with all 278 Boolean operations on ≤3 variables (elegant u16 encoding)
- ✅ Factory pattern implemented for construction
- ⚠️ Still uses concrete `NodeByte` in main evaluation path instead of `BooleanSimpleOp`
- ❌ Missing u16/u32/u64/u128 implementations for UnsignedBits
- ❌ **Zero tests written**

### Architectural Goals
1. **Trait abstractions over concrete types**: ✅ Mostly achieved with generics
2. **Factory pattern for construction**: ✅ Fully implemented (NodeFactory, MetavariableFactory, TermFactory)
3. **Math correctness first**: ❌ **No tests written** - Critical gap
4. **Support 10+ Boolean variables**: ⚠️ Partial (u8 + BigUint only, missing u128 for 7 vars)

---

## Phase 0: Document Factory Pattern Use - ⚠️ 50% Complete

**Status**: Implementation complete, documentation missing

**What's been implemented:**
- ✅ `NodeFactory` trait in `src/node/factory.rs`
- ✅ `MetavariableFactory` trait in `src/metavariable/factory.rs`
- ✅ `TermFactory` trait in `src/term/factory.rs`
- ✅ `NodeByteFactory` concrete implementation (174 lines, stateless with PhantomData)
- ✅ Factory methods demonstrated in metavariable/meta_byte.rs

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

#### Documentation (0% Complete)
- [ ] Document factory pattern rationale in module-level docs
- [ ] Provide examples of stateful vs. stateless factory implementations
- [ ] Document how factories enable different construction strategies
- [ ] Add examples showing factory usage for different backends (testing, production, database)

#### Design Considerations for Later (Not Blocking)
- [ ] Consider `StatementFactory` trait (Statements are serialized for long-term storage)
- [ ] Consider factory trait for substitutions/unifications
- [ ] Plan for Rc/Arc integration in concrete factory implementations
- [ ] Design caching strategy for term deduplication

**Files to examine:**
- `src/node/factory.rs` - NodeFactory trait
- `src/metavariable/factory.rs` - MetavariableFactory trait (has good documentation)
- `src/term/factory.rs` - TermFactory trait
- `src/node/node_byte/factory.rs` - Concrete example of stateless factory

---

## Phase 1: UnsignedBits Implementations - ⚠️ 40% Complete

**Status**: Core infrastructure complete, missing 4 key integer types and all tests

**What's been implemented:**
- ✅ `UnsignedBits<U, const N: usize>` trait defined (src/bool_eval_next/mod.rs:1105)
- ✅ `<bool; 0>` implementation (single bit)
- ✅ `<u8; 0..=3>` generic implementation (1, 2, 4, 8 bits for 0-3 variables)
- ✅ `<BigUint; N>` via `SomeBits<N>` wrapper (with bigint feature, proper `Not` via XOR mask)

### Special Cases
- ✅ `<bool; 0>`: Single bit, implemented
- ✅ `<BigUint; N>`: Arbitrary N, `Not` implemented as `mask XOR value`

### Generic uXXX Pattern (Macro Candidate)
The pattern `<uXXX; N>` for unsigned integer types should be generalized via macro:
- ✅ `<u8; 0..=3>`: 1, 2, 4, 8 bits (0-3 variables) - IMPLEMENTED
- ❌ `<u16; 0..=4>`: 1, 2, 4, 8, 16 bits (0-4 variables) - MISSING
- ❌ `<u32; 0..=5>`: 1, 2, 4, 8, 16, 32 bits (0-5 variables) - MISSING
- ❌ `<u64; 0..=6>`: 1, 2, 4, 8, 16, 32, 64 bits (0-6 variables) - MISSING
- ❌ `<u128; 0..=7>`: 1, 2, 4, 8, 16, 32, 64, 128 bits (0-7 variables) - **CRITICAL MISSING**

**Action Items**:
- [ ] **CRITICAL**: Add `<u128; 0..=7>` implementation (required for 7 Boolean variable support)
- [ ] Add `<u16; 0..=4>` implementation
- [ ] Add `<u32; 0..=5>` implementation
- [ ] Add `<u64; 0..=6>` implementation
- [ ] Design macro to reduce code duplication for `<uXXX; N>` pattern
  - **Decision**: Explicitly call out each `(type, N)` pair - no math in macros to keep them readable
  - Example: `impl_unsigned_bits!(u128, 0); impl_unsigned_bits!(u128, 1); ... impl_unsigned_bits!(u128, 7);`
- [ ] Verify native bitwise ops (`BitAnd`, `BitOr`, `BitXor`, `Not`) work correctly for new types
- [ ] **CRITICAL**: Write unit tests for each implementation (truth table verification)

---

## Phase 2: BooleanNode Trait Abstraction - ✅ 75% Complete

**Status**: Excellent infrastructure implemented, but not integrated into main evaluation path

**What's been implemented (Better than originally specified!):**
- ✅ `BooleanSimpleOp` enum (src/bool_eval_next/mod.rs:30-665) - **All 278 Boolean operations on ≤3 variables**
  - Elegant encoding: `u16 = 0x{arity}_{truth_table_code}`
  - Example: `AndAB2 = 0x2_88` (arity=2 in upper bits, code=0x88 in lower 8 bits)
  - Complete enumeration: 2 nullary + 4 unary + 16 binary + 256 ternary = 278 total
- ✅ `get_arity()` method - extracts arity from upper bits
- ✅ `get_code3()` method - extracts 8-bit truth table code
- ✅ `eval0/1/2/3<B, U, const N>()` methods - generic evaluation for any `UnsignedBits<U, N>`
- ✅ `BooleanSimpleNode<Ty>` wrapper (line 665) - implements `Node` trait, generic over any `Type` system

**What's missing:**
- ❌ Main `eval_boolean_*` functions still pattern match on `NodeByte::*` directly (not using BooleanSimpleOp)
- ❌ No trait abstraction allowing other node types to provide evaluation codes
- ❌ Not exported from lib.rs (internal infrastructure only)
- ❌ No conversion between `NodeByte` ↔ `BooleanSimpleOp`

**Note**: The `BooleanSimpleOp` design is architecturally superior to the original TODO proposal - it provides exhaustive enumeration rather than a trait. Integration is the remaining work.

### Original Design (for reference)
The TODO proposed replacing hard-coded `NodeBytes` enum matching with trait-based dispatch:

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

**Action Items (Updated based on actual implementation)**:
- [ ] Integrate `BooleanSimpleOp` into main evaluation path (replace `NodeByte::*` pattern matching)
- [ ] Consider: Define `BooleanNode` trait to allow both `NodeByte` and `BooleanSimpleOp` to coexist
- [ ] Add conversion: `TryFrom<NodeByte> for BooleanSimpleOp` (or vice versa)
- [ ] Export `BooleanSimpleOp` and `BooleanSimpleNode<Ty>` from lib.rs if useful publicly
- [ ] Complete the `eval3()` implementation (many `todo!()` macros for ternary operations)
- [ ] Document the elegant u16 encoding scheme in module-level docs

**Original Action Items (for reference)**:
- [~] Define `BooleanNode` trait in `src/node/boolean.rs` - SUPERSEDED by BooleanSimpleOp enum
  - **Decision**: Place in node module since nodes represent more than just Boolean operations
  - Create file if it doesn't exist, add to `src/node/mod.rs` exports
- [~] Refactor `eval_boolean_node` to accept `<N: BooleanNode>` generic parameter - PARTIALLY done
- [~] Pattern match on `(u8, arity)` tuples instead of `NodeBytes::*` variants - INFRASTRUCTURE ready
- [~] Document mapping from NodeBytesLogicTable.md codes to evaluation behavior - PARTIALLY done

---

## Phase 3: NewTerm Trait Abstraction - ✅ 90% Complete

**Status**: Exceeded expectations - went straight to production `Term` trait instead of temporary prototype

**What's been implemented:**
- ✅ `EnumTerm<T, V, N>` enum in `src/term/simple.rs` (150 lines)
  - `Leaf(V)` - metavariable leaf variant
  - `NodeOrLeaf(N, Vec<Self>)` - node head with children
- ✅ Implements production `Term<Ty, V, N>` trait from `src/term/base.rs`
- ✅ Fully generic over Type, Metavariable, and Node
- ✅ `Display` implementation for debugging
- ✅ Serde support (with feature)
- ✅ `eval_boolean_term` accepts generic `EnumTerm<Ty, V, No>` where `No: Node + TryInto<NodeByte>`
- ✅ Pattern matching on enum variants works cleanly (no need for trait methods)

**Minor improvements possible:**
- [ ] Consider adding convenience methods `as_metavariable()`, `as_node()` per original design notes
  - Current pattern matching approach works fine, this is just polish

**Decision made**: Skipped temporary "NewTerm" prototype and went directly to production `Term` trait implementation. This is better long-term architecture.

### Original Context (RESOLVED)
- ~~Previous `Term` trait (in `src/term/base.rs`) exists but is not functional enough~~ ✅ NOW FUNCTIONAL
- ~~`EnumTerm<V, NodeBytes>` concrete type was easier to work with (had `MetaLeaf`, `NodeHead` variants)~~ ✅ IMPLEMENTED
- ~~Need trait-based abstraction for `bool_eval_next` that doesn't couple to concrete types~~ ✅ ACHIEVED with generics

### Original Design Goals (ALL MET)
- ✅ Support term traversal (distinguish metavariable leaves from node heads)
- ✅ Access child terms recursively
- ✅ Query node type (via generic `N: Node` bound)
- ✅ Integrated with main `Term` trait (not temporary)

### Original Open Questions (ANSWERED)
- ✅ Pattern matching on enum variants is clean and idiomatic Rust
- ✅ Generic over `T: Type`, `V: Metavariable<Type = T>`, `N: Node<Type = T>`
- ✅ No visitor pattern needed for this use case

**Original Action Items (ALL COMPLETED)**:
- [x] Design `NewTerm` trait with minimal sufficient interface for evaluation
  - **Actual**: Went directly to production `Term` trait - better decision
- [x] Refactor `eval_boolean_term` to use generic terms
- [x] Generic over both `V` (metavariable) and `N` (node) ✅
- [x] Works with main `Term` trait

---

## Phase 4: Integration and Testing - ❌ 20% Complete (CRITICAL BLOCKER)

**Status**: Module structure complete, but **ZERO TESTS WRITTEN** - violates "Math Correctness First" principle

### Compilation
- [x] Fix all import errors in `src/bool_eval_next/mod.rs` - module now compiles
- [x] Resolve `num-bigint` dependency issues (feature gating) - properly gated with `#[cfg(feature = "bigint")]`
- [x] Module re-enabled in lib.rs (line 53)
- [ ] **Not verified**: `cargo +1.77 build --all-features` - needs to be run

### Testing Strategy (Math Correctness First!) - ❌ 0% COMPLETE
**CRITICAL GAP**: Zero tests in the entire 3,690-line commit

- [ ] **CRITICAL**: Unit tests for `UnsignedBits` trait implementations
  - Verify `mask()`, `n()`, `from_orig()`, `set_bit()` for each type
  - Test bitwise operations match truth tables
  - Verify `from_bool()` creates correct patterns
- [ ] **CRITICAL**: Integration tests for Boolean evaluation
  - Simple expressions: `Not(True)`, `And(True, False)`, etc.
  - Tautologies: `Or(A, Not(A))` should always evaluate to `mask()` (all 1s)
  - Non-tautologies: `And(A, Not(A))` should always be 0
  - ~~7-variable expressions using `u128` backend~~ (blocked: u128 not implemented)
  - 10-variable expressions using `BigUint` backend (with `bigint` feature)
- [ ] Regression tests against previous NodeBytes implementation (if available)
- [ ] Test `BooleanSimpleOp` evaluation methods (`eval0/1/2/3`)
- [ ] Test edge cases:
  - Arity mismatch (node expects 2 children, gets 3)
  - Variable not in binding list
  - Unknown Boolean operation codes

### Code Quality Gates - ⚠️ NOT RUN
- [ ] `cargo +1.77 clippy --all-features --all-targets`
- [ ] `cargo +1.77 doc --all-features`
- [ ] `cargo +1.77 test --all-features`

**Recommendation**: Do not merge until at least basic tests are written for:
1. UnsignedBits trait implementations (bool, u8, SomeBits)
2. Simple Boolean evaluation (True, False, Not, And, Or)
3. Tautology detection (Law of Excluded Middle)

---

## Summary of Staged Changes

**Total impact**: 3,690 additions / 101 deletions across 23 files

### New Files Created (7 files, 2,525 lines)
| File | Lines | Status | Notes |
|------|-------|--------|-------|
| `src/node/node_byte/base.rs` | 1,375 | ✅ Complete | NodeByte enum with 222+ operations |
| `src/node/node_byte/factory.rs` | 174 | ✅ Complete | NodeByteFactory implementation |
| `src/node/node_byte/NodeByteTable.md` | 289 | ✅ Complete | Documentation of 256 Boolean operations |
| `src/node/node_byte/mod.rs` | 7 | ✅ Complete | Module declarations |
| `src/metavariable/enums.rs` | 273 | ✅ Complete | AsciiMetaVar implementation |
| `src/metavariable/meta_byte.rs` | 136 | ✅ Complete | MetaByte implementation |
| `src/term/simple.rs` | 150 | ✅ Complete | EnumTerm<T, V, N> implementation |
| `src/bool_eval_next/mod.rs` (major expansion) | +1,152 | ⚠️ 60% | Needs u128/tests |

### Modified Files (15 files, major changes)
| File | Change | Status | Notes |
|------|--------|--------|-------|
| `src/lib.rs` | Exports updated | ✅ Complete | Re-enabled bool_eval_next module |
| `src/metavariable/mod.rs` | Trait relaxed | ✅ Complete | Removed `Copy` requirement |
| `Cargo.toml` | Dependencies | ✅ Complete | Added `strum` for enums |
| `README.md` | Badges added | ✅ Complete | License + downloads |

### Deleted Files (1 file)
- `src/node/enums.rs` - Replaced by `node_byte/` submodule

### Architecture Highlights
1. **Factory pattern fully implemented** - NodeFactory, MetavariableFactory, TermFactory traits
2. **BooleanSimpleOp infrastructure** - All 278 Boolean operations with elegant u16 encoding
3. **Generic evaluation** - Decoupled from concrete bit representations via `UnsignedBits<U, N>` trait
4. **Production-ready Term abstraction** - EnumTerm implements main Term trait

---

## Future Work (Post bool_eval_next)

### Term Trait Unification
- ✅ ~~Merge `NewTerm` design lessons into main `Term` trait~~ - ALREADY DONE
- ✅ ~~Ensure single unified trait works for all use cases~~ - EnumTerm implements Term trait
- ✅ ~~Remove temporary `NewTerm` abstraction~~ - Never created, went straight to production

### Statement Trait-Based Redesign (Future consideration)
- Currently `Statement` is a concrete struct
- May need trait-based approach for Rust-style inheritance

### NodeByte/BooleanSimpleOp Integration
- ✅ ~~Implement full `NodeBytes` enum with 222 named operations~~ - DONE (NodeByte has 222+)
- ✅ BooleanSimpleOp has all 278 Boolean operations on ≤3 variables
- [ ] Integrate BooleanSimpleOp into main evaluation path
- [ ] Consider trait to unify NodeByte and BooleanSimpleOp approaches
- ✅ ~~Maintain backward compatibility with previous design~~ - Factory pattern provides this

### Serialization and Database Integration (Future)
- Design node representation for serializable theorem databases
- Connect to Metamath and condensed detachment tools
- Trait-based abstraction to support multiple backends
- Factory pattern already in place to support this

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

### BigUint Special Handling - ✅ IMPLEMENTED
✅ `BigUint` doesn't have native `Not` trait support - implemented manually in `SomeBits<N>`:
- ✅ Uses `mask XOR value` pattern (src/bool_eval_next/mod.rs:1494)
- ✅ Mask computed based on N: `(BigUint::from(1u32).pow(1 << N)) - 1`
- ✅ Custom `Not` implementation for `SomeBits<N>` wrapper type
- ✅ All bitwise ops implemented: `BitAnd`, `BitOr`, `BitXor`, `Not`

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
