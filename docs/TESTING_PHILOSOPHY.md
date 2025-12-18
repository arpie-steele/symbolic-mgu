# Testing Philosophy

This document articulates the testing philosophy for symbolic-mgu, addressing fundamental constraints in testing theorem-proving systems and documenting coverage status.

## The Oracle Problem

Statement operations (APPLY, CONTRACT, CONDENSED_DETACH) face a fundamental testing challenge: **there is no oracle to predict which operations should succeed.**

### The Problem

**Property-based testing faces inherent limitations:**

1. **Generating valid test cases requires solving the problem being tested**
   - Testing "tautology → operation → tautology" requires generating valid operation applications
   - But determining which applications are valid is the problem we're trying to verify

2. **Structural constraints limit testable combinations**
   - With axioms Simp (1), Frege (2), Transp (3), we can test:
     - D11, D12, D13, D21, D22, D23 (6 combinations work)
   - But cannot test:
     - D31, D32, D33 (structural incompatibility: Transp has ¬φ in consequent, won't unify with →)
   - No general algorithm exists to predict which combinations unify successfully

3. **Novel operations lack validation corpora**
   - CONTRACT is a novel operation with no historical precedent
   - No existing corpus of "correct CONTRACT operations" exists for validation
   - Cannot rely on literature or reference implementations

### The Solution

Given these fundamental constraints, symbolic-mgu employs a three-pronged testing strategy:

**1. Correctness by Construction**
- Built on proven-correct primitives:
  - Unification: 8 property-based tests covering all core properties
  - Type system: comprehensive type safety validation
  - Normal form maintenance: 7 tests plus idempotence properties
- If primitives are correct and operations correctly apply them, soundness follows

**2. Empirical Validation**
- **100+ Principia Mathematica proofs** serve as our oracle
- Historical proofs validated by mathematicians provide real-world test cases
- All derived theorems verified as tautologies using truth tables
- This corpus provides strong empirical evidence of soundness

**3. Comprehensive Structural Testing**
- 30 unit tests cover Statement operations (CONTRACT, APPLY, CANONICALIZE, etc.)
- Error cases: invalid indices, type mismatches, unification failures
- Success cases: operations that structurally can succeed
- Edge cases: empty statements, placeholders, boundary conditions
- Regression tests: real bugs found and fixed (e.g., disjointness enforcement)

### Conclusion

> "There is no royal road to geometry." — Attributed to Euclid

The testing approach is appropriate given fundamental constraints. Property-based testing of arbitrary operation applications is impossible without an oracle. The combination of correctness-by-construction, empirical validation via historical proofs, and comprehensive structural testing provides strong confidence in implementation soundness.

## Test Coverage Status (v0.1.0)

### Thoroughly Tested

**Unification and Substitution:**
- Robinson's unification with occurs check
- 8 property-based test suites (commutativity, idempotence, type safety, etc.)
- Cycle detection and prevention
- Normal form maintenance (7 dedicated tests)

**Type System:**
- Type safety enforcement (Boolean/Setvar/Class)
- Subtyping rules (Setvar ⊆ Class)
- Disjointness validation (Boolean disjoint from others)
- Dedicated test suite: `tests/type_capability_validation.rs`

**Statement Operations:**
- 30 unit tests covering all operations
- Error handling, success cases, edge cases
- Property: canonicalization preserves logical meaning (mutual inclusion)
- Regression tests for discovered bugs

**Boolean Evaluation:**
- 30 functional completeness tests
- All 16 two-variable Boolean functions
- Validates all minimal functionally complete operator sets
- BigUint support for 8-20 variables tested

**Compact Proof System:**
- 9 parser unit tests (error handling, edge cases)
- PM corpus validation (100+ historical proofs)
- Regression tests for disjointness bugs
- Tautology/validity verification tested

### Awaiting First-Order Logic

**Distinctness Graphs:**
- Basic operations tested (graph primitives, edge management)
- Simple test cases exist with Setvar constraints
- **Stress testing awaits first-order logic and set theory**
  - Propositional logic rarely uses distinctness constraints
  - Quantifiers (∀, ∃) are where distinctness becomes critical
  - Variable capture prevention needs quantified formulas
  - Will be tested organically during Metamath integration

**Rationale:** Current testing validates correctness of the distinctness graph implementation. Comprehensive stress testing requires first-order logic formulas with quantifiers, which will come naturally when validating Metamath proofs (1910 PM) and integrating set.mm database.

### Explicitly Deferred

**Serialization (serde):**
- Feature exists but not intended for production use yet
- Types have `Serialize`/`Deserialize` derives for future work
- **Deferred until database integration with Rc/Arc**
- Current derives may need custom implementations for reference types
- No round-trip tests until serialization format stabilizes

**Rationale:** Database integration will introduce Rc/Arc references for shared Metamath objects. Serialization strategy depends on final architecture. Testing now would validate unstable/incomplete functionality.

### Not Testable via Automation

**Documentation Accuracy:**
- Cannot automate verification that prose matches implementation
- Requires human comprehension and semantic reasoning
- Natural language understanding beyond current technology

**What IS tested:**
- Documentation builds without warnings (`cargo doc`)
- Code examples in docs compile (96 doc tests pass)
- Doc links resolve correctly
- 30+ documentation lints enforced

**Maintained through:**
- Code review
- Quality gate: `cargo +1.77 doc --all-features`
- User feedback and issue reports
- Regular maintenance (documented in git history)

## Quality Gates

All tests must pass before commit:

1. `cargo +1.77 test --all-features` — 120 unit + 27 integration + 96 doc tests
2. `cargo +1.77 clippy --all-features --all-targets` — No warnings
3. `cargo +1.77 doc --all-features` — Builds without warnings
4. `cargo +1.77 fmt --check` — Code formatted

**Note:** All commands use `+1.77` to enforce MSRV (Minimum Supported Rust Version).

## Testing Philosophy Summary

1. **Correctness by construction** — Build on proven-correct primitives
2. **Empirical validation** — Use historical proofs as oracle
3. **Comprehensive structural testing** — Test all paths within structural constraints
4. **Accept fundamental limitations** — Some tests are impossible (oracle problem)
5. **Defer unstable features** — Test when architecture stabilizes
6. **Acknowledge automation limits** — Some validation requires human judgment

This approach balances rigor with pragmatism, providing strong confidence in correctness while acknowledging the fundamental constraints in testing theorem-proving systems.
