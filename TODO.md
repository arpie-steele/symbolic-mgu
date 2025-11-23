# symbolic-mgu TODO List

## 📊 Overall Progress: ~99% Complete

**Summary of v010 branch status (as of v0.1.0-alpha.12):**

| Phase | Status | Completion | Notes |
|-------|--------|------------|-------|
| Phase 0: Factory Pattern | ✅ Complete | 100% | Comprehensive documentation added |
| Phase 1: UnsignedBits | ✅ Complete | 100% | All types implemented and tested |
| Phase 2: BooleanSimpleOp | ✅ Complete | 100% | Fully implemented, exported, tested |
| Phase 3: Term Abstraction | ✅ Complete | 100% | Generic Term trait support |
| Phase 4: Testing | ✅ Complete | 100% | 24 tests covering all operations |
| Phase 5: Unification | ✅ Complete | 100% | Robinson's MGU fully backported |
| Phase 6: Enhanced Testing API | ✅ Complete | 100% | test_term(), test_contradiction(), test_satisfiable(), TruthTable |
| Phase 7: rustmgu Backport | ✅ Complete | 100% | All features backported and tested |

**Status for v0.1.0 final release:**
- ✅ **All tests passing** - 233 tests total (90 unit + 31 validation/integration + 1 PM validation + 95 doc + 16 new)
  - 90 lib unit tests (includes 12 formatter tests)
  - 12 property-based tests (unification_properties.rs)
  - 4 regression tests (regression_compact_proofs.rs)
  - 6 conversion tests (statement_conversion.rs)
  - 9 term invariant tests (term_invariants.rs) - NEW
  - 10 type capability tests (type_capability_validation.rs) - NEW
  - 3 formatter stress tests (formatter_stress_test.rs) - NEW
  - 4 custom formatter tests (custom_formatter_test.rs) - NEW
  - 1 PM proofs validation test (2,882 proofs, ignored by default - run with --ignored)
  - 95 doctests (all passing)
- ✅ **All UnsignedBits types** - bool, u8, u16, u32, u64, u128, BigUint
- ✅ **Unification algorithm** - Substitution, MGU, occurs check
- ✅ **Statement operations** - substitute, apply, contract
- ✅ **Compact binary** - Working with verification and formatter support
- ✅ **Regression tests** - DDD111D23, DDD1D221D2D2D11 validate disjointness fix
- ✅ **ParametricMetavariable** - Generic metavariable with flexible decoration (Phase 7.9)
  - Replaced WideMetavariable with more general design
  - Generic over Type system, decorator type (subscripts/primes), and character set
  - New types: WideCharSet, Prime, Decorator
  - 12 Boolean, 24 Setvar, 24 Class characters in WideCharSet
  - Formatter integration complete (format_with() implemented)
- ✅ **Output formatters** - 6 formatters implemented (Phase 7.10)
  - ASCII, UTF-8, UTF-8-color, HTML, HTML-color, LaTeX
  - Global formatter registry with OnceLock (zero dependencies)
  - Type-based coloring for metavariables
  - Integrated with compact binary (--format flag)
- ✅ **Quality gates pass** - clippy, doc, test all clean (zero warnings)
- ✅ **Property-based testing** - 12 comprehensive tests using proptest 1.5.0
  - Commutativity, idempotence, reflexivity of unification
  - Type safety with correct Setvar ⊆ Class subtyping
  - Occurs check, structural compatibility
- ✅ **v0.1.0-alpha.11 major changes:**
  - Upgraded to strum-0.27.2
  - New Statement::canonicalize() method
  - Ord trait added to Metavariable, Node, Term, Type (supports canonicalization)
  - Macro for testing BooleanSimpleOp against primitive unsigned ints (wider testing)
  - Replaced WideMetavariable with more general ParametricMetavariable
  - Moved test_validity (of Statements) from compact binary to bool_eval module
  - Removed Default trait requirement from many implementations
  - crate::bool_eval::generated_enum now private module, BooleanSimpleOp re-exported from bool_eval
  - WideMetavariable constants exported under new names
  - New types: WideCharSet, Prime, Decorator for ParametricMetavariable
  - MetaByte simplification: Truly ASCII-only (returns literal characters like "P")
- ✅ **v0.1.0-alpha.12 API validation (2025-11-14):**
  - Completed all high-priority API stability validation tasks (see docs/ALPHA12_RECOMMENDATIONS.md)
  - Term trait audit: Removed `todo!()`, added 9 property tests validating invariants
  - Type capability validation: 10 tests verifying capability-based design works correctly
  - Panic audit: Documented all unwraps with SAFETY comments or improved error messages (7 files)
  - Formatter stress testing: Validated with 100+ variables and deep nesting (50+ levels)
  - Custom formatter API: Verified third parties can implement OutputFormatter trait
- ⚠️ **Documentation gaps** - Module docs exist but could be expanded
- 🚧 **Backporting from rustmgu** - See Phase 7 below

---

## Current Status: bool_eval Module Complete

### Implementation Summary
The `bool_eval` module is feature-complete and tested:
- ✅ `EnumTerm` type implemented in `src/term/simple.rs` (150 lines)
- ✅ `NodeByte` enum implemented with 222+ operations in `src/node/node_byte/base.rs` (1,375 lines)
- ✅ `BooleanSimpleOp` enum with all 278 Boolean operations on ≤3 variables (elegant u16 encoding)
- ✅ Factory pattern implemented for construction
- ✅ All UnsignedBits implementations: bool, u8, u16, u32, u64, u128, BigUint
- ✅ **5 comprehensive tests** covering all 278 operations on bool, u8, u64, BigUint
- ✅ **All quality gates passing** (clippy, doc, test)

### Architectural Goals - All Met
1. **Trait abstractions over concrete types**: ✅ Achieved with UnsignedBits<U, N> trait
2. **Factory pattern for construction**: ✅ Fully implemented (NodeFactory, MetavariableFactory, TermFactory)
3. **Math correctness first**: ✅ Tests verify all 278 Boolean operations
4. **Support 10+ Boolean variables**: ✅ u128 supports 7 vars, BigUint supports arbitrary N

### BooleanSimpleOp Design Note
`BooleanSimpleOp` is exported publicly but intended to be largely internal. Future work will add a `Node` method mapping nodes to `Option<BooleanSimpleOp>` for tautology searches and proof verification.

---

## Phase 0: Document Factory Pattern Use - ✅ 100% Complete

**Status**: Implementation and documentation complete

**What's been implemented:**
- ✅ `NodeFactory` trait in `src/node/factory.rs` with comprehensive documentation
- ✅ `MetavariableFactory` trait in `src/metavariable/factory.rs` with comprehensive documentation
- ✅ `TermFactory` trait in `src/term/factory.rs` with comprehensive documentation
- ✅ `NodeByteFactory` concrete implementation (stateless example)
- ✅ `MetaByteFactory` concrete implementation (stateless example)
- ✅ `EnumTermFactory` concrete implementation (stateless example)

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

**Documentation added (v0.1.0-alpha.9):**
- ✅ NodeFactory module-level docs: 180 lines of rationale, examples, and patterns
- ✅ MetavariableFactory module-level docs: 190 lines covering variable management
- ✅ TermFactory module-level docs: 290 lines on term construction and caching
- ✅ All examples tested as doctests (35 doctests passing)
- ✅ Stateful vs stateless factory patterns explained with examples
- ✅ Different backend examples (testing, production, database) documented
- ✅ Usage patterns for all three factory types

---

### Action Items - All Complete

#### Documentation (100% Complete)
- [x] Document factory pattern rationale in module-level docs
- [x] Provide examples of stateful vs. stateless factory implementations
- [x] Document how factories enable different construction strategies
- [x] Add examples showing factory usage for different backends (testing, production, database)

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

## Phase 1: UnsignedBits Implementations - ✅ 95% Complete

**Status**: All implementations complete and tested via `ub_prim_impl!` macro

**What's been implemented:**
- ✅ `UnsignedBits<U, const N: usize>` trait defined (src/bool_eval/mod.rs)
- ✅ `<bool; 0>` implementation (single bit)
- ✅ `<u8; 0..=3>` implementations (4 total: 1, 2, 4, 8 bits for 0-3 variables)
- ✅ `<u16; 0..=4>` implementations (5 total: supports 0-4 variables)
- ✅ `<u32; 0..=5>` implementations (6 total: supports 0-5 variables)
- ✅ `<u64; 0..=6>` implementations (7 total: supports 0-6 variables)
- ✅ `<u128; 0..=7>` implementations (8 total: supports 0-7 variables)
- ✅ `<BigUint; N>` via `SomeBits<N>` wrapper (with bigint feature, proper `Not` via XOR mask)

### Implementation Details
- ✅ **Macro-based**: `ub_prim_impl!` macro defined in `src/macros.rs` reduces duplication
- ✅ **31 macro invocations**: Generates all primitive type implementations
- ✅ **Bitwise operations**: All native ops (`BitAnd`, `BitOr`, `BitXor`, `Not`) verified via tests
- ✅ **Tests**: 5 comprehensive tests verify all 278 BooleanSimpleOp operations

### Coverage
| Type | Variables | Bits | Status |
|------|-----------|------|--------|
| `bool` | 0 | 1 | ✅ Tested |
| `u8` | 0-3 | 1-8 | ✅ Tested |
| `u16` | 0-4 | 1-16 | ✅ Implemented |
| `u32` | 0-5 | 1-32 | ✅ Implemented |
| `u64` | 0-6 | 1-64 | ✅ Tested |
| `u128` | 0-7 | 1-128 | ✅ Implemented |
| `BigUint` | N | 2^N | ✅ Tested |

**Remaining work**:
- [ ] (Optional) Add integration tests specifically for u16, u32, u128 (currently only bool, u8, u64, BigUint tested)
- [ ] (Optional) Document the `ub_prim_impl!` macro usage pattern

---

## Phase 2: BooleanSimpleOp Implementation - ✅ 90% Complete

**Status**: Fully implemented, exported, and tested

**What's been implemented:**
- ✅ `BooleanSimpleOp` enum (src/bool_eval/generated_enum.rs) - **All 278 Boolean operations on ≤3 variables**
  - Elegant encoding: `u16 = 0x{arity}_{truth_table_code}`
  - Example: `AndAB2 = 0x2_88` (arity=2 in upper bits, code=0x88 in lower 8 bits)
  - Complete enumeration: 2 nullary + 4 unary + 16 binary + 256 ternary = 278 total
- ✅ `get_arity()` method - extracts arity from upper bits
- ✅ `get_code3()` method - extracts 8-bit truth table code
- ✅ `eval0/1/2/3<B, U, const N>()` methods - generic evaluation for any `UnsignedBits<U, N>`
- ✅ `BooleanSimpleNode<Ty>` wrapper - implements `Node` trait, generic over any `Type` system
- ✅ **Exported from lib.rs** - `pub use bool_eval::generated_enum::BooleanSimpleOp;`
- ✅ **Comprehensive tests** - All 278 operations tested on bool, u8, u64, BigUint

**Design Note:**
`BooleanSimpleOp` is architecturally superior to the original trait-based proposal - it provides exhaustive enumeration with compile-time guarantees. The enum is exported publicly but intended to be largely internal. Future work will add a `Node` method: `fn to_boolean_op(&self) -> Option<BooleanSimpleOp>` for tautology searches and proof verification.

**Remaining work:**
- [x] (v0.1.0-alpha.12) Add `TryFrom<NodeByte> for BooleanSimpleOp` conversion - **COMPLETE**
- [ ] (Future) Add `Node::to_boolean_op()` method for generic node types

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
- [ ] (Future) Integrate `BooleanSimpleOp` into main evaluation path (replace `NodeByte::*` pattern matching)
- [ ] (Future) Consider: Define `BooleanNode` trait to allow both `NodeByte` and `BooleanSimpleOp` to coexist
- [x] Add conversion: `TryFrom<NodeByte> for BooleanSimpleOp` - **COMPLETE (v0.1.0-alpha.12)**
- [x] Export `BooleanSimpleOp` and `BooleanSimpleNode<Ty>` from lib.rs - **COMPLETE**
- [x] Complete the `eval3()` implementation (all 256 ternary operations fully implemented)
- [ ] (Future) Document the elegant u16 encoding scheme in module-level docs

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
- ~~Need trait-based abstraction for `bool_eval` that doesn't couple to concrete types~~ ✅ ACHIEVED with generics

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

## Phase 4: Integration and Testing - ✅ 70% Complete

**Status**: Comprehensive tests implemented and passing

### Compilation - ✅ Complete
- ✅ All import errors fixed in `src/bool_eval/mod.rs`
- ✅ `num-bigint` dependency properly feature-gated with `#[cfg(feature = "bigint")]`
- ✅ Module exported in lib.rs
- ✅ **Verified**: `cargo +1.77 build --all-features` - builds successfully

### Testing Strategy - ✅ 70% Complete

**5 comprehensive tests implemented** in `src/bool_eval/mod.rs`:

1. ✅ **`all_variants_make_truth_tables`** - Tests all 278 operations on `bool` type
   - Verifies each operation's truth table matches its code
   - Tests eval0/1/2/3 methods for all arities

2. ✅ **`all_variants_u8_truth_tables`** - Tests all 278 operations on `u8` with N=3
   - Uses standard test vectors: a=0xaa, b=0xcc, c=0xf0
   - Verifies bitwise operations produce correct truth tables

3. ✅ **`all_variants_u64_truth_tables`** - Tests all 278 operations on `u64` with N=3
   - Extended test vectors across 64 bits
   - Validates large integer operations

4. ✅ **`all_variants_bigint_truth_tables`** - Tests all 278 operations on `BigUint` (with `bigint` feature)
   - Validates arbitrary-precision arithmetic
   - Tests SomeBits<N> wrapper implementation

5. ✅ **`specific_operations`** - Spot checks common operations
   - Tests constants (True/False)
   - Tests binary ops (And, Or, Xor, NotAnd)
   - Tests ternary ops (Or3, And3, Xor3, Majority3)

**Test Coverage:**
- ✅ All 278 BooleanSimpleOp operations tested
- ✅ UnsignedBits implementations: bool, u8, u64, BigUint
- ✅ All eval0/1/2/3 methods tested
- ✅ Truth table verification for all operations
- ⚠️ u16, u32, u128 implementations not explicitly tested (but should work identically)

### Code Quality Gates - ✅ Complete
- ✅ `cargo +1.77 clippy --all-features --all-targets` - No warnings
- ✅ `cargo +1.77 doc --all-features` - Documentation builds
- ✅ `cargo +1.77 test --all-features` - All 21 tests pass (up from 12)

**Remaining work:**
- [ ] (Optional) Add tests specifically for u16, u32, u128
- [ ] (Optional) Add integration tests for eval_boolean_term
- [ ] (Optional) Add edge case tests (arity mismatch, unknown vars)

---

## Phase 5: Unification Backport - ✅ 100% Complete

**Status**: Successfully backported from rustmgu (edition 2024) to symbolic-mgu (edition 2018)

**What's been implemented:**
- ✅ `Substitution<V, T>` type (src/term/substitution.rs lines 1-183)
  - HashMap-based variable → term mapping
  - Methods: new, get, extend, contains, len, is_empty, iter, iter_mut
  - `ensure_acyclic()` - cycle detection with depth-first search

- ✅ `NormalizingSubstitution<V, N, T, TF>` type (lines 185-363)
  - Maintains normal form invariant (no variable chains)
  - `try_normalize()` - safe promotion from Substitution
  - `extend()` - adds binding and renormalizes all existing mappings

- ✅ Unification functions (lines 365-617)
  - `occurs_check()` - prevents cyclic substitutions like x ↦ f(x)
  - `apply_substitution()` - recursively applies substitution to terms
  - `unify()` - public MGU entry point (Robinson's algorithm)
  - `unify_with_subst()` - recursive unification with accumulator

- ✅ Statement operations enhanced (src/statement/mod.rs)
  - `substitute()` - applies substitution to entire statement (line 256)
  - `apply()` - applies one statement to another (line 470)
  - `contract()` - Meredith's condensed detachment (line 300)

- ✅ Distinctness graphs backported (from edition 2024)
  - `src/distinct/pair.rs` (222 lines)
  - `src/distinct/simple_graph.rs` (110 lines)
  - Enhanced `src/distinct/mod.rs` (81 lines)

**Test Coverage** (9 new tests in src/term/substitution.rs:619-790):
1. ✅ `empty_substitution` - Basic substitution operations
2. ✅ `single_binding` - Variable mapping
3. ✅ `identical_terms_unify` - Identity unification
4. ✅ `different_variables_unify` - Variable-to-variable unification
5. ✅ `type_mismatch_fails` - Type system enforcement
6. ✅ `occurs_check_detects_cycle` - Cycle detection works
7. ✅ `occurs_check_prevents_unification` - Prevents x ↦ f(x)
8. ✅ `apply_substitution_to_var` - Simple substitution
9. ✅ `apply_substitution_to_node` - Recursive substitution on compound terms

**Key Features:**
- Full Robinson's unification algorithm with occurs check
- Type-aware unification (respects Boolean/Setvar/Class hierarchy)
- Normal form maintenance (no variable chains)
- Edition 2018 compatible (all let-chains rewritten)
- No new external dependencies

**Architecture:**
- Factory pattern integration for flexible term construction
- Unified file structure (substitution + unification in one file)
- Comprehensive error handling with MguError
- Generic over Type, Metavariable, Node, and Term traits

### Action Items

✅ **All Complete** - No remaining work

**Future Considerations (Optional):**
- [ ] Add more Statement integration tests (multi-step proofs)
- [ ] Document factory pattern usage examples
- [ ] Consider caching strategy for term deduplication

---

## Phase 6: Enhanced Boolean Testing API - ✅ 100% Complete

**Status**: Comprehensive API for testing Boolean term properties (v0.1.0-alpha.7)

**What's been implemented:**
- ✅ `test_term<T>(term: &T) -> Result<Option<bool>, MguError>` - Core evaluation function
  - Returns `Ok(Some(true))` for **tautologies** (true for all assignments)
  - Returns `Ok(Some(false))` for **contradictions** (false for all assignments)
  - Returns `Ok(None)` for **contingent** formulas (mixed truth values)
  - Generic over any `T: Term<Ty, V, No>` implementation
  - Automatic type selection based on variable count (0-20 vars)

- ✅ `test_tautology<T>(term: &T) -> Result<bool, MguError>` - Convenience wrapper
  - Returns `true` if term is a tautology
  - Implemented as: `test_term(term).map(|opt| opt == Some(true))`

- ✅ `test_contradiction<T>(term: &T) -> Result<bool, MguError>` - Contradiction checker
  - Returns `true` if term is always false
  - Implemented as: `test_term(term).map(|opt| opt == Some(false))`

- ✅ `test_contingent<T>(term: &T) -> Result<bool, MguError>` - Contingency checker
  - Returns `true` if term is neither tautology nor contradiction
  - Implemented as: `test_term(term).map(|opt| opt.is_none())`

**Key Improvements:**
- **Generic Term support**: Works with any `Term` implementation, not just `EnumTerm`
- **More information**: Single evaluation distinguishes tautologies, contradictions, and contingent formulas
- **Memory efficiency**: Optimized for 8-19 variables (uses appropriate SomeBits<N> size)
- **Clean API**: Core function + three simple wrappers
- **Comprehensive documentation**: Parallel documentation for all helper functions

**Architecture Benefits:**
- Single implementation serves multiple use cases
- Easy to add new helpers (e.g., `test_satisfiable()`)
- Aligns with "trait abstractions first" principle
- Zero runtime overhead (generic monomorphization)

### Test Coverage

**3 integration tests** in `src/bool_eval/mod.rs`:
1. ✅ `tautology_simple()` - Law of excluded middle: `p ∨ ¬p` → Some(true)
2. ✅ `tautology_not_tautology()` - Contradiction: `p ∧ ¬p` → Some(false)
3. ✅ `tautology_de_morgan()` - De Morgan's law → Some(true)

**Quality Gates**: ✅ All passing
- All 24 tests pass
- No clippy warnings
- Documentation builds successfully
- Edition 2018 compatible (Rust 1.77+)

### Action Items

✅ **All Complete** - No remaining work

---

## Phase 7: rustmgu Feature Backport - ✅ 100% Complete

**Status**: Backporting mature features from rustmgu (edition 2024) to symbolic-mgu (edition 2018)

### Overview

The rustmgu codebase (v0.6.0, edition 2024) contains several production-quality features that should be backported to symbolic-mgu. This includes theorem proving infrastructure (compact proof parsing, statement inclusion), enhanced statement operations, comprehensive testing, and the compact binary for proof verification.

**Key Architectural Difference**: symbolic-mgu's factory pattern is a superior design NOT present in rustmgu. We will adapt rustmgu code to work with our factory-based architecture rather than adopting rustmgu's direct construction approach.

**Design Decision**: We will NOT implement rustmgu's `InfallibleMetavariable` and `InfallibleNodeCore` traits. These traits provide panic-on-error versions of fallible operations, but we prefer to plan for failure using Result types consistently throughout the codebase.

### Backport Progress

**What's been completed:**
- ✅ proptest 1.5.0 added to dev-dependencies (compatible with Rust 1.77+/edition 2018)
- ✅ Verified edition 2018 compatibility (all let-chains can be rewritten)
- ✅ Analysis complete: 75% of rustmgu core already backported

**What's completed:**
- ✅ Logic module enhancements (Phase 7.1)
- ✅ Compact proof parsing (Phase 7.2)
- ✅ Statement inclusion checking (Phase 7.3)
- ✅ Statement module refactoring (Phase 7.4)
- ✅ Additional operations (Phase 7.5)
- ✅ Compact binary (Phase 7.7)

**What's planned:**
- ⏳ S-expression support (Term::to_sexp()) - Optional
- ⏳ Integration tests (PM proofs, property tests)

### 7.1: Logic Module Enhancements - ✅ 100% Complete

**Goal**: Add helper functions and constants for working with fundamental logical statements.

**What's been implemented:**

1. ✅ **Modus Ponens Constants** (src/logic/mod.rs lines 14-19)
   ```rust
   /// Index of minor premise (φ) in Modus Ponens hypotheses
   pub const MP_MINOR_PREMISE: usize = 0;

   /// Index of major premise (φ → ψ) in Modus Ponens hypotheses
   pub const MP_MAJOR_PREMISE: usize = 1;
   ```

2. ✅ **Statement Dictionary Builder** (src/logic/mod.rs lines 388-419)
   ```rust
   /// Build standard statement dictionary for compact proofs
   /// Uses MetavariableFactory for flexible metavariable creation
   pub fn create_dict<MF, N>(
       metavar_factory: &MF,
       implies_node: N,
       not_node: N,
   ) -> Result<Dictionary<MF::Metavariable, N>, MguError>
   where
       MF: MetavariableFactory<MetavariableType = SimpleType>,
       MF::Metavariable: Metavariable<Type = SimpleType> + Default,
       N: Node<Type = SimpleType>,
   ```

3. ✅ **Generic helper functions** - modus_ponens(), simp(), frege(), transp() (already existed)

**Design Decisions:**
- Used MetavariableFactory pattern instead of requiring enumerate() method
- Made create_dict() fully generic over factory and node types
- Dictionary type alias for cleaner signatures
- Comprehensive rustdoc with examples

**Complexity**: Low (60 lines implemented)
**Dependencies**: None (uses existing statement builders)
**Priority**: ⭐⭐⭐ **HIGH** (blocking compact proof parsing) - **COMPLETE**

**Action Items:**
- [x] Add MP_MINOR_PREMISE and MP_MAJOR_PREMISE constants to src/logic/mod.rs
- [x] Implement create_dict() function using MetavariableFactory
- [x] Add rustdoc with examples
- [x] Export from lib.rs (already pub mod logic)
- [x] All tests passing (19 doctests pass)

### 7.2: Compact Proof Parsing - ✅ 100% Complete

**Goal**: Parse compact proof strings (e.g., "D__", "DD211") into Statement objects.

**What's been implemented:**

1. ✅ **apply_multiple() Method** (src/statement/mod.rs lines 530-656)
   - Applies multiple proofs to multiple hypotheses simultaneously
   - Relabels all proofs to avoid variable conflicts
   - Builds combined substitution incrementally
   - Merges hypotheses and distinctness graphs

2. ✅ **Compact Proof Parser** (src/statement/compact_proof.rs, 168 lines)
   ```rust
   pub fn from_compact_proof<VF, TF>(
       proof: &str,
       var_factory: &VF,
       term_factory: &TF,
       statements: &HashMap<String, Self>,
   ) -> Result<Self, MguError>
   ```
   - Right-to-left stack-based processing
   - Placeholder support ("_" for unsatisfied hypotheses)
   - Token parsing and validation
   - Comprehensive error messages

3. ✅ **Test Suite** (9 unit tests + 1 doctest)
   - ✅ test_d_with_placeholders - Placeholder semantics
   - ✅ test_dd211_phi_implies_phi - Complete proof (φ → φ)
   - ✅ test_empty_proof_fails - Error handling
   - ✅ test_invalid_token_fails - Character validation
   - ✅ test_unknown_statement_key_fails - Dictionary lookup
   - ✅ test_stack_underflow_fails - Stack validation
   - ✅ test_incomplete_proof_fails - Final validation
   - ✅ test_axioms_directly - Direct axiom access
   - ✅ test_final_placeholder_fails - None rejection

**Design Decisions:**
- Integrated with factory pattern (requires both var_factory and term_factory)
- Uses UnificationFailure for all errors (no ParseError enum needed)
- Placeholder (None) support for partial proofs
- Stack-based evaluation matches mathematical convention (right-to-left)

**Complexity**: Medium (~200 lines implemented)
**Dependencies**: create_dict(), apply_multiple() - **ALL COMPLETE**
**Priority**: ⭐⭐⭐ **CRITICAL** - **COMPLETE**

**Action Items:**
- [x] Create src/statement/compact_proof.rs
- [x] Implement apply_multiple() for efficient hypothesis satisfaction
- [x] Port from_compact_proof() method with factory pattern support
- [x] Add comprehensive rustdoc with working examples
- [x] Write comprehensive unit tests (33 total passing)
- [x] All tests passing (including doctests)

### 7.3: Statement Inclusion - ✅ 100% Complete

**Goal**: Check if one statement logically includes another (subsumption/α-equivalence).

**What's been implemented:**

1. ✅ **is_included_in() Method** (src/statement/inclusion.rs lines 97-225)
   - Checks if `self ⊆ other` (self is included in other)
   - **Critical relabeling** to avoid occurs-check failures
   - Unifies assertions and extends substitution
   - Matches hypotheses incrementally
   - Verifies distinctness graph preservation

2. ✅ **is_identical() Method** (lines 278-295)
   - Checks α-equivalence via mutual inclusion
   - S₁ ≡ S₂ iff (S₁ ⊆ S₂ and S₂ ⊆ S₁)

3. ✅ **transform_distinctness_graph_static() Helper** (lines 306-345)
   - Transforms distinctness graphs under substitution
   - Expands edges when variables map to compound terms

4. ✅ **Comprehensive Test Suite** (8 tests)
   - ✅ axiom_included_in_itself - Reflexivity
   - ✅ axiom_identical_to_itself - Identity reflexivity
   - ✅ more_specific_included_in_general - Substitution specialization
   - ✅ different_variables_same_structure_are_identical - α-equivalence
   - ✅ hypothesis_order_doesnt_matter - Set semantics
   - ✅ more_hypotheses_with_distinctness - Distinctness prevents collapsing
   - ✅ unrelated_structures_not_included - Incompatible structures
   - ✅ relabeling_prevents_occurs_check_failure - Critical relabeling test

**Design Decisions:**
- Factory-based implementation (requires var_factory and term_factory parameters)
- Variable relabeling before unification prevents false negatives
- Incremental substitution extension for hypothesis matching
- Comprehensive module-level documentation explaining inclusion semantics

**Complexity**: Medium (~350 lines implemented with tests)
**Dependencies**: Unification, apply_substitution, relabel_disjoint - **ALL PRESENT**
**Priority**: ⭐⭐⭐ **HIGH** - **COMPLETE**

**Action Items:**
- [x] Create src/statement/inclusion.rs with comprehensive docs
- [x] Implement is_included_in() with relabeling support
- [x] Implement is_identical() using mutual inclusion
- [x] Implement distinctness graph transformation
- [x] Write comprehensive unit tests (41 total passing)
- [x] Add working doctest examples
- [x] All tests passing (including 2 doctests)
**Dependencies**: unify() (already present), substitute() (already present)
**Priority**: ⭐⭐⭐ **HIGH** (fundamental for proof verification)

**Action Items:**
- [ ] Create src/statement/inclusion.rs
- [ ] Port is_included_in() from rustmgu
- [ ] Port is_identical() from rustmgu
- [ ] Adapt for factory pattern if needed
- [ ] Add rustdoc examples from rustmgu
- [ ] Write unit tests

### 7.4: Statement Module Refactoring - ✅ 100% Complete

**Goal**: Organize statement operations into separate files like rustmgu.

**Completed Structure** (v0.1.0-alpha.9):
```
src/statement/
├── mod.rs           # Module exports and documentation
├── base.rs          # Statement struct, new(), simple_axiom(), accessors (152 lines)
├── substitution.rs  # substitute, transform_distinctness_graph (157 lines)
├── operations.rs    # apply, contract, relabel_disjoint, apply_multiple (353 lines)
├── compact_proof.rs # from_compact_proof (from 7.2)
└── inclusion.rs     # is_included_in, is_identical (from 7.3)
```

**Complexity**: Low (mostly moving code around)
**Dependencies**: None (pure refactoring) - **COMPLETE**
**Priority**: ⭐⭐ **MEDIUM** (improves organization) - **COMPLETE**

**Action Items:**
- [x] Create src/statement/base.rs (Statement struct + core methods)
- [x] Create src/statement/operations.rs (apply, contract, relabel_disjoint)
- [x] Create src/statement/substitution.rs (substitute, transform_distinctness_graph)
- [x] Update src/statement/mod.rs to re-export from submodules
- [x] Verify all tests still pass (41 unit tests, 35 doctests)
- [x] No clippy warnings

### 7.5: Additional Statement Operations - ✅ 100% Complete

**Goal**: Add operations for efficient proof construction.

**What's been implemented:**

1. ✅ **apply_multiple** (src/statement/operations.rs lines 298-400)
   - Applies multiple statements to multiple hypotheses simultaneously
   - Relabels all proofs to avoid variable conflicts
   - Builds combined substitution incrementally
   - More efficient than sequential apply() calls

2. ✅ **condensed_detach** (src/statement/operations.rs lines 460-497)
   - Meredith's condensed detachment operation
   - Creates fresh modus ponens instance and applies two statements
   - Uses MP_MINOR_PREMISE and MP_MAJOR_PREMISE constants for clarity
   - Fully documented with working doctest

**Complexity**: Low (builds on existing operations) - **COMPLETE**
**Dependencies**: apply(), contract(), modus_ponens() - **ALL PRESENT**
**Priority**: ⭐⭐ **MEDIUM** - **COMPLETE**

**Action Items:**
- [x] Add apply_multiple() to src/statement/operations.rs (already done in 7.2)
- [x] Add condensed_detach() to src/statement/operations.rs
- [x] Adapt for factory pattern
- [x] Add rustdoc examples with working doctest
- [x] All tests passing (41 unit tests, 36 doctests)

### 7.6: S-Expression Support - ⏳ 0% Complete

**Goal**: Add human-readable serialization format for terms.

**File to create**: `src/term/sexp.rs` (~50 lines)

**Key Method**:
```rust
pub trait Term<Ty, V, N> {
    /// Convert term to S-expression string
    /// Example: (→ (∧ p q) r)
    fn to_sexp(&self) -> String;
}
```

**Complexity**: Low (pure formatting)
**Dependencies**: None
**Priority**: ⭐ **LOW** (nice-to-have for compact binary output)

**Action Items:**
- [ ] Create src/term/sexp.rs
- [ ] Add to_sexp() trait method to Term
- [ ] Implement for EnumTerm
- [ ] Add unit tests

### 7.7: Compact Binary - ✅ 100% Complete

**Goal**: Command-line tool for processing compact proofs and verifying theorems.

**What's been implemented:**

1. ✅ **src/bin/compact.rs** (186 lines)
   - Command-line argument parsing
   - Help text and usage examples
   - Compact proof processing using from_compact_proof()
   - Display results with clear formatting
   - Optional verification with --verify flag

2. ✅ **Validity checking** (check_validity function)
   - For theorems (no hypotheses): Verifies assertion is a tautology
   - For inferences (has hypotheses): Verifies H₁ → (H₂ → (... → (Hₙ → A))) is a tautology
   - Checks if all terms are Boolean type before verification
   - Clear output messages distinguishing tautologies from valid inferences

3. ✅ **Exported test functions** from lib.rs
   - test_tautology, test_contradiction, test_contingent, test_term
   - Now available as part of public API

**Features implemented:**
- ✅ Process compact proof strings
- ✅ Display results with clear formatting (using Display trait)
- ✅ Verify tautologies for theorems using test_tautology()
- ✅ Verify validity for inferences (hypotheses entail assertion)
- ✅ Multiple proof processing in single invocation
- ✅ Comprehensive help text with verification explanation

**Complexity**: Low - **COMPLETE**
**Dependencies**: compact_proof.rs (7.2) ✓, create_dict() (7.1) ✓ - **ALL PRESENT**
**Priority**: ⭐⭐⭐ **HIGH** - **COMPLETE**

**Testing:**
```bash
# Basic usage
cargo run --bin compact -- DD211

# Verify theorem is a tautology
cargo run --bin compact -- --verify DD211
# Output: ✓ Verified: This is a tautology

# Verify inference is valid
cargo run --bin compact -- --verify D__
# Output: ✓ Valid: Hypotheses logically entail the assertion

# Multiple proofs
cargo run --bin compact -- D__ DD211 DD2D111
```

**Note**: `src/bin/` remains in Cargo.toml exclude list but binary builds successfully with explicit `--bin compact` flag.

**Action Items:**
- [x] Create src/bin/compact.rs
- [x] Adapt for factory pattern (uses MetaByteFactory and EnumTermFactory)
- [x] Add command-line help text
- [x] Test with sample proofs (D__, DD211, DD2D111 all working)
- [x] Export test_tautology and related functions from lib.rs
- [x] Implement validity checking for inferences (H₁ → H₂ → ... → A)
- [x] Enhanced help text explaining tautology vs validity verification
- [x] All tests passing (41 unit tests, 36 doctests)
- [ ] Document usage in README.md (future enhancement)

### 7.8: Integration Tests - ✅ 100% Complete

**Goal**: Add comprehensive integration tests from rustmgu.

**What's been implemented:**

1. ✅ **tests/unification_properties.rs** (407 lines)
   - 12 comprehensive property-based tests using proptest 1.5.0
   - Core unification properties: commutativity, idempotence, reflexivity
   - Safety properties: occurs check, type safety, structural compatibility
   - Covers all fundamental properties of Robinson's unification algorithm

2. ✅ **tests/regression_compact_proofs.rs** (4 tests)
   - Validates DDD111D23 and DDD1D221D2D2D11 proofs
   - Verifies disjointness bug fix (relabel_disjoint before unification)
   - Tests compact proof parsing end-to-end

3. ✅ **tests/pmproofs_validation.rs** (validates 2,882 proofs from subproofs.json)
   - Validates all Principia Mathematica subproofs
   - Tests compact proof parsing with real-world examples
   - Verifies each proof produces a tautology or valid inference
   - Marked #[ignore] due to 22-second runtime; run with --ignored flag

4. ✅ **tests/statement_conversion.rs** (6 tests)
   - Tests Statement::convert() cross-implementation conversion
   - MetaByte ↔ WideMetavariable round-trip conversion
   - Distinctness graph preservation
   - Exhaustion error handling (>11 Boolean variables)

**Complexity**: Complete
**Priority**: ⭐⭐⭐ **HIGH** - **COMPLETE**

**Action Items:**
- [x] Add regression tests for DDD111D23 and DDD1D221D2D2D11
- [x] Create tests/unification_properties.rs
- [x] Define proptest strategies for Term
- [x] Create tests/pmproofs_validation.rs
- [x] Integrate subproofs.json tests (verify each produces tautology)
- [x] Create tests/statement_conversion.rs

### 7.9: ParametricMetavariable Implementation - ✅ 100% Complete (v0.1.0-alpha.11)

**Goal**: Implement generic ParametricMetavariable to replace WideMetavariable with more flexible design.

**What's been implemented:**

1. ✅ **ParametricMetavariable<Ty, U, CharSet>** (src/metavariable/parametric.rs)
   - Generic over Type system (Ty), decorator type (U), and character set
   - Display: base char from CharSet + optional decorator (subscripts, primes, etc.)
   - Supports any decoration style via type parameter U

2. ✅ **Decorator Types** (src/metavariable/decorator.rs)
   - `()` - No decoration (φ, ψ, χ)
   - `usize` - Numeric subscripts (φ, φ₁, φ₂...)
   - `u8` - Compact subscripts (0-255)
   - `Prime` - Prime notation (φ, φ′, φ″, φ‴)

3. ✅ **WideCharSet Type** (src/metavariable/charset.rs)
   - Character set abstraction for ASCII/UTF-8/LaTeX representations
   - Compile-time const arrays (zero cost, no trait overhead)
   - Constants for Boolean (12 chars), Setvar (24 chars), Class (24 chars)
   - Mathematical Italic Unicode: 𝜑𝜓𝜒... (Greek), 𝑥𝑦𝑧... (lowercase), 𝐴𝐵𝐶... (uppercase)

4. ✅ **Character Constants Exported**
   - Exported under new names from crate root
   - Available for use with ParametricMetavariable

5. ✅ **Factory Pattern Integration**
   - Factory implementation for ParametricMetavariable
   - Stateless implementation
   - Enumeration support

**Design Benefits:**
- Type-independent: Works with any Type trait implementation, not just SimpleType
- Flexible decorators: Choose decoration style via type parameter
- Format-agnostic storage: Same struct for all output formats
- Zero-cost abstraction: Compile-time const arrays
- Human-readable enumeration: Cycles base characters first, then decorators

**Migration from WideMetavariable:**
- WideMetavariable fully replaced by ParametricMetavariable
- All tests updated and passing
- More general and extensible design

**Complexity**: Medium (~600 lines across multiple files)
**Dependencies**: None (pure addition)
**Priority**: ⭐⭐⭐ **HIGH** - **COMPLETE**

**Action Items:**
- [x] Create src/metavariable/parametric.rs
- [x] Create src/metavariable/decorator.rs (Prime, Decorator trait)
- [x] Create src/metavariable/charset.rs (WideCharSet)
- [x] Implement ParametricMetavariable with generic type parameters
- [x] Add formatter support (format_with() implementation)
- [x] Replace all WideMetavariable usage with ParametricMetavariable
- [x] Export character constants under new names
- [x] Update tests
- [x] All quality gates passing

### 7.10: Output Formatter System - ✅ 100% Complete

**Goal**: Implement extensible output formatters for multiple target formats.

**Design Document**: See `docs/FORMATTER_DESIGN.md` and `FORMATTER_DEMO_SUMMARY.md`

**What's been implemented:**

1. ✅ **Core Formatter Trait** (src/formatter/output_formatter.rs)
   - `OutputFormatter` trait with delegation pattern
   - Object-safe design (works with `dyn OutputFormatter`)
   - Color getter methods: `get_boolean_color()`, `get_setvar_color()`, `get_class_color()`
   - Infix/prefix notation support via `is_infix()` method

2. ✅ **Type-Color Registry** (src/formatter/type_colors.rs)
   - Simple `Color` struct with xterm256 + HTML hex (no dependencies)
   - Global `TYPE_COLOR_REGISTRY` with `OnceLock<RwLock<HashMap>>` (zero dependencies)
   - Default colors: Boolean→Blue (#0088ff/33), Setvar→Green (#00aa00/34), Class→Red (#cc0000/160)
   - Public API: `register_type_color()`, `get_type_color()`, `get_type_color_from_trait()`

3. ✅ **Global Formatter Registry** (src/formatter/registry.rs)
   - `GLOBAL_FORMATTER_REGISTRY` with `OnceLock<RwLock<HashMap<String, Arc<dyn OutputFormatter>>>>`
   - 6 built-in formatters registered on first access
   - Public API: `register_formatter()`, `get_formatter()`
   - Fallback to Display formatter for unknown names

4. ✅ **Enhanced Metavariable Trait** (src/metavariable/mod.rs)
   - Added `format_with(&dyn OutputFormatter) -> String` method
   - Added `to_ascii()` and `to_utf8()` helper methods
   - Default implementation delegates to Display trait

5. ✅ **Enhanced Node Trait** (src/node/base.rs)
   - Added `format_with(&dyn OutputFormatter) -> String` method
   - Added `to_ascii_symbol()`, `to_utf8_symbol()`, `to_latex_symbol()` methods
   - Implemented for NodeByte (40+ operators in all formats)

6. ✅ **Built-in Formatters** (src/formatter/formatters.rs)
   - `AsciiFormatter`: Metamath baseline (ph, ps, ch; ->, -., /\, \/)
   - `Utf8Formatter`: Plain Unicode (φ, ψ, χ; →, ¬, ∧, ∨)
   - `Utf8ColorFormatter`: ANSI 256-color terminal with type-based coloring
   - `HtmlFormatter`: Plain HTML with Unicode symbols
   - `HtmlColorFormatter`: Inline styles with proper `<sub>` tags for subscripts
   - `LatexFormatter`: LaTeX math mode (\varphi, \to, \land, \lor)

7. ✅ **Concrete Implementations**
   - **MetaByte**: Simplified to return literal characters (P, Q, x, A)
   - **ParametricMetavariable**: Full formatter support with flexible decoration
     - UTF-8: Unicode subscript digits (₀₁₂...) or primes (′″‴)
     - HTML: Proper `<sub>` tags with normal digits
     - ASCII: Underscore notation (ph_1, ph_2...)
     - LaTeX: Subscript notation (\varphi_1, \varphi_2...)
     - Supports different decorator types: usize, u8, Prime, ()
   - **NodeByte**: 40+ operators in ASCII, UTF-8, LaTeX formats
   - **EnumTerm**: Recursive formatting with proper parenthesization

8. ✅ **Compact Binary Integration** (src/bin/compact.rs)
   - Added `--format=<name>` flag with 6 supported formats
   - Updated help text with formatter descriptions
   - Examples work: `--format=ascii`, `--format=utf8-color`, `--format=html-color`

9. ✅ **Test Suite** (src/formatter/tests.rs)
   - 12 comprehensive tests covering all formatters
   - Tests for metavariables, nodes, terms
   - Tests for complex nested expressions
   - Tests for color capability checking

10. ✅ **Bug Fixes** (during implementation)
    - Fixed UTF-8 color: subscripts now included in ANSI escape sequences
    - Fixed HTML: uses proper `<sub>` tags with normal digits (not Unicode subscripts)

**Implementation Details:**
- Zero external dependencies (uses stdlib `OnceLock` and `RwLock`)
- Object-safe trait design via delegation pattern
- Thread-safe lazy initialization for both registries
- Generic throughout (works with any Type/Node/Metavariable implementation)
- Comprehensive documentation with examples

**Complexity**: ~1200 lines implemented across 8 files

**Priority**: ⭐⭐⭐ **HIGH** - **COMPLETE**

**Action Items:**
- [x] Create src/formatter/ module hierarchy
- [x] Implement Color and TYPE_COLOR_REGISTRY (OnceLock, no dependencies)
- [x] Implement GLOBAL_FORMATTER_REGISTRY (OnceLock, object-safe)
- [x] Add format_with() to Metavariable trait
- [x] Add format_with() + symbol methods to Node trait
- [x] Implement MetaByte simplified (returns literal characters)
- [x] Implement MetaByte formatter support (all 6 formats)
- [x] Implement ParametricMetavariable formatter support (with flexible decoration)
- [x] Implement NodeByte symbol methods (40+ operators)
- [x] Implement 6 built-in formatters
- [x] Add --format flag to compact binary
- [x] Write comprehensive formatter tests (12 tests)
- [x] Document formatter API in module docs
- [x] Export formatter API from lib.rs
- [x] Fix subscript coloring bug (UTF-8 ANSI escapes)
- [x] Fix HTML subscript bug (use <sub> tags, not Unicode)
- [x] Create demonstration script and summary document
- [ ] ~~Implement Formatted<T> wrapper~~ (deferred to v0.2.0)

**Post-Implementation Example:**
- [ ] **Meredith Paper Parser Example** - Demonstrate parsing/verifying historical logic papers
  - Parse Meredith's 1953 (A,N) system paper examples in Polish notation
  - Verify all theorems using `test_tautology()`
  - Display in multiple formats: Polish, infix, UTF-8, LaTeX
  - Example: `CCpqCCqrCpr` → verified tautology → displayed as:
    - Polish: `CCpqCCqrCpr`
    - Infix: `((p → q) → ((q → r) → (p → r)))`
    - UTF-8: `((φ → ψ) → ((ψ → χ) → (φ → χ)))`
    - LaTeX: `((\varphi \to \psi) \to ((\psi \to \chi) \to (\varphi \to \chi)))`
  - Shows how modern tooling can illuminate historical papers
  - Educational fair use (brief quotes + independent verification)
  - Reference: https://en.wikipedia.org/wiki/Polish_notation
  - See also: Łukasiewicz (1929) *Elementy logiki matematycznej* and Bocheński's 16-connective system

**Documentation Updates:**
- [ ] Add Polish notation reference to `BooleanSimpleOp` module docs
  - Link to https://en.wikipedia.org/wiki/Polish_notation
  - Document correspondence: Cpq (implication), Npq (negation), Apq (or), Kpq (and), Epq (equivalence)
  - Note Łukasiewicz (1929) as original source
  - Mention Bocheński's systematic 16-connective extension organized by truth value frequency

**Design Principles:**
- Only metavariables colored by Type
- Avoid elaborate color theory (no CIE XYZ/Lab)
- Statement layout is application-controlled
- HTML uses inline styles (no CSS assumptions)
- Delegation to Node/Metavariable format_with() methods

### Dependencies Graph

```
7.1 create_dict()
  └─> 7.2 compact_proof.rs
       └─> 7.7 compact binary
       └─> 7.8 PM tests

7.3 inclusion.rs ───> 7.8 PM tests

7.4 refactoring (independent)

7.5 operations ───> 7.8 equivalence tests

7.6 sexp (optional for 7.7)

proptest ✓ ───> 7.8 property tests
```

**Critical Path for v0.1.0-alpha.8**:
1. 7.1 (create_dict) → 2. 7.2 (compact_proof) → 3. 7.7 (compact binary)

**Suggested Implementation Order**:
1. ✅ Add proptest dev-dependency (DONE)
2. 🚧 7.1: Logic enhancements (MP constants, create_dict)
3. 7.2: Compact proof parsing
4. 7.3: Statement inclusion
5. 7.7: Compact binary (depends on 7.1, 7.2)
6. 7.8: Integration tests (PM proofs, property tests)
7. 7.4: Refactoring (cleanup)
8. 7.5: Additional operations (polish)
9. 7.6: S-expressions (polish)

### Estimated Effort

**Week 1**: Logic enhancements (7.1) + Compact proofs (7.2) + Inclusion (7.3)
**Week 2**: Compact binary (7.7) + Property tests (7.8 partial)
**Week 3**: PM tests (7.8) + Additional operations (7.5)
**Week 4**: Refactoring (7.4) + Polish + Documentation

**Total**: ~4 weeks for complete Phase 7

### Quality Gates

All backported code must meet:
- ✅ `cargo +1.77 check --all-features --all-targets`
- ✅ `cargo +1.77 clippy --all-features --all-targets` (no warnings)
- ✅ `cargo +1.77 doc --all-features` (builds successfully)
- ✅ `cargo +1.77 test --all-features` (all tests pass)
- ✅ Edition 2018 compatible (no let-chains, no edition 2021 syntax)
- ✅ Rust 1.77+ compatible

---

## Summary - v010 Branch Ready for v0.1.0 Final Release

**Branch status**: Feature-complete and ready for v0.1.0 final release

### Key Accomplishments

**BooleanSimpleOp Module - Complete:**
- ✅ All 278 Boolean operations implemented (2 nullary + 4 unary + 16 binary + 256 ternary)
- ✅ Generic `UnsignedBits<U, N>` trait for bool, u8, u16, u32, u64, u128, BigUint
- ✅ 5 comprehensive tests covering all operations on multiple backends
- ✅ Quality gates passing (clippy, doc, test)
- ✅ Exported publicly from lib.rs

**Factory Pattern Infrastructure:**
- ✅ NodeFactory, MetavariableFactory, TermFactory traits
- ✅ NodeByteFactory concrete implementation (stateless)
- ✅ EnumTerm<T, V, N> production-ready term representation

**Unification System - Complete:**
- ✅ Robinson's MGU algorithm with occurs check
- ✅ Substitution and NormalizingSubstitution types
- ✅ Type-aware unification (Boolean/Setvar/Class hierarchy)
- ✅ Statement operations (substitute, apply, contract)
- ✅ Distinctness graphs for preventing invalid substitutions
- ✅ 9 comprehensive tests covering all core scenarios
- ✅ Edition 2018 compatible (all let-chains rewritten)

**Documentation:**
- ✅ Module-level documentation in bool_eval/mod.rs
- ✅ Macro documentation in src/macros.rs (updated with correct examples)
- ✅ NodeByteTable.md documenting Boolean operations
- ✅ Archived planning documents in docs/archive/
  - BACKPORT_PLAN.md (unification backport)
  - BOOL_EVAL_BACKPORT_PLAN.md (tautology testing)
  - GENERIC_TAUTOLOGY_PLAN.md (generic Term support)
- ⚠️ Factory pattern usage could be better documented

### Release Readiness (v0.1.0 Final)

**Ready for v0.1.0 final release:**
- ✅ Math correctness verified (207 tests including PM proofs validation)
- ✅ All target architectures supported (bool through BigUint)
- ✅ Clean code quality (no clippy warnings)
- ✅ Documentation builds successfully
- ✅ Public API stable and minimal
- ✅ Comprehensive test suite (unit, integration, property-based, regression)
- ✅ All major features implemented and tested

**Optional enhancements for future releases:**
- [ ] Expand factory pattern documentation
- [ ] Add usage examples for BooleanSimpleOp
- [ ] Document README.md usage patterns

---

## Future Work (Post bool_eval)

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
// In src/bool_eval/mod.rs (temporary location)

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
/// with the bool_eval evaluation engine by mapping to
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
├── bool_eval/
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
- ✅ Uses `mask XOR value` pattern (src/bool_eval/mod.rs:1494)
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
