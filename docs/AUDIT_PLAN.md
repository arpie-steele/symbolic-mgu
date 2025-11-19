# Documentation and Testing Audit Plan

**Date**: 2025-11-15
**Status**: Phases 1 & 2 Complete - v0.1.0 Release Ready
**MSRV**: Rust 1.77.0 - ALL testing must use this toolchain

## Audit Progress Summary

**Completed** ✅:
- Phase 1: Documentation Audit (FormalSpec vs Implementation, Trait Documentation)
- Phase 2: Testing Audit - Statement Operations (27 new tests added)
  - Test count: 90 → 117 tests
  - All Statement operations now have comprehensive coverage
  - Weeks 1-3 testing complete (error cases, properties, edge cases, success cases)
  - All quality gates passing (test, clippy, doc, fmt with Rust 1.77)

**Optional Future Work** ⏸:
- Phase 3: API Review for Database Compatibility (not required for v0.1.0)
- Week 4: Additional property tests (nice to have)
- Additional coverage: Boolean evaluation, distinctness graphs (future enhancements)

## Critical: MSRV Enforcement

**Minimum Supported Rust Version**: 1.77.0

### All Commands Must Use Explicit Toolchain

```bash
# CORRECT - Always specify +1.77
cargo +1.77 test --all-features
cargo +1.77 clippy --all-features --all-targets
cargo +1.77 doc --all-features
cargo +1.77 build --all-features

# WRONG - Don't use default toolchain
cargo test    # Could use 1.82, hiding MSRV issues
```

### Why This Matters

1. **Avoid accidental feature use**: Newer Rust versions add language features and stdlib APIs
2. **Ensure compatibility**: Users on Rust 1.77 must be able to build the crate
3. **Catch issues early**: Better to find MSRV violations during development

### Install Toolchain

```bash
rustup install 1.77.0
rustup default 1.77.0  # Optional: make it default for this project
```

### CI/CD Requirement

Any CI pipeline must test with Rust 1.77.0 explicitly.

---

## Audit Scope

### Phase 1: Documentation Audit
Verify documentation is accurate, complete, and accessible.

### Phase 2: Testing Audit
Identify gaps in test coverage and add missing tests.

### Phase 3: API Review
Check API for future database compatibility.

---

## Phase 1: Documentation Audit ✅ COMPLETED

**Findings**: See AUDIT_FINDINGS.md for full details

### 1.1 FormalSpec.md vs Implementation ✅ COMPLETED

**Status**: All operations verified and documented

**Check**:
- CONTRACT operation matches `src/statement/operations.rs`
- APPLY operation matches implementation
- Inclusion/Identity definitions accurate
- Canonical form algorithm correct
- Distinctness graph behavior matches
- Substitution and unification definitions accurate

**Method**:
1. Read FormalSpec.md section by section
2. Find corresponding implementation
3. Run tests with `cargo +1.77 test`
4. Verify behavior matches specification

**Deliverable**: ✅ Confirmation of alignment documented in AUDIT_FINDINGS.md

### 1.2 Trait Documentation Completeness ✅ COMPLETED

**Status**: Term trait fully documented and tested

**Files**: `src/term/base.rs`, `src/mgutype/type_trait.rs`, `src/metavariable/mod.rs`, `src/node/base.rs`

**Check for each trait**:
- All public methods documented
- Examples compile with Rust 1.77
- Error conditions documented
- Trait purpose clearly explained

**Method**:
```bash
cargo +1.77 doc --all-features --open
# Review each trait's documentation
```

**Deliverable**: ✅ Term trait improvements documented in AUDIT_FINDINGS.md

### 1.3 Public API Examples ✅ COMPLETED

**Status**: All examples verified with Rust 1.77

**Check**:
- Statement operations have usage examples
- Unification examples
- Substitution examples
- DistinctnessGraph examples
- Boolean evaluation examples
- All examples compile with Rust 1.77

**Method**:
```bash
cargo +1.77 test --doc --all-features
```

**Deliverable**: ✅ All examples compile with Rust 1.77

### 1.4 Academic Accessibility ✅ COMPLETED

**Status**: Documentation reviewed and improved

**Files**: All `*.md` in `src/` and `docs/`

**Check**:
- Terminology appropriate for target audience (math historians, mathematicians, CS researchers)
- No unnecessary jargon
- Citations properly formatted
- Mathematical notation consistent

**Deliverable**: ✅ Improvements documented in AUDIT_FINDINGS.md

---

## Phase 2: Testing Audit ⏳ IN PROGRESS

**Current Status**: Statement operations testing complete (18 tests), additional areas pending

### 2.1 Current Test Coverage ✅ COMPLETED

**Status**: Coverage gaps identified and documented in PHASE2_TEST_COVERAGE.md

**Commands**:
```bash
cargo +1.77 test --all-features
cargo +1.77 test --all-features -- --nocapture  # See output
```

**Check**:
- Which modules have low coverage
- Which critical paths untested

**Deliverable**: Coverage gaps identified

### 2.2 Edge Cases: Unification

**Missing tests** (in `src/term/substitution.rs`):
- Unify identical terms
- Occurs check violation
- Type mismatch
- Deeply nested terms
- Already-substituted terms
- Empty substitution
- Circular substitution attempt

**Method**: Write tests, verify with `cargo +1.77 test`

### 2.3 Edge Cases: Statement Operations ✅ COMPLETE

**Status**: 27 tests implemented (see TEST_GAPS_PLAN.md for full details)

**CONTRACT tests** ✅ (8 tests total):
- ✅ Equal indices error
- ✅ Out-of-bounds indices error
- ✅ Unification failure (different operators)
- ✅ Empty distinctness graph (Week 3)
- ✅ Duplicate hypotheses result (Week 3)
- ✅ Identical hypotheses success (Week 2)
- ✅ Unifiable variables success (Week 2)
- Note: Type incompatibility prevented by type system (unreachable)
- Note: Distinctness violations adequately covered via APPLY tests

**APPLY tests** ✅ (5 tests total):
- ✅ Out-of-bounds index error
- ✅ Unification failure
- ✅ Simple axiom application (Week 3)
- ✅ All hypotheses consumed (Week 3)
- ✅ Metavariable collision (existing regression test maintained)
- Note: Type mismatch prevented by type system (unreachable)

**APPLY_MULTIPLE tests** ✅ (4 tests total):
- ✅ Empty proofs error
- ✅ Too few proofs error
- ✅ Too many proofs error
- ✅ Modus ponens pattern success (Week 3)

**CONDENSED_DETACH tests** ✅ (4 tests total):
- ✅ Non-implication major premise error
- ✅ Unifiable metavariables success case
- ✅ Classic modus ponens (Week 3)
- ✅ With substitution (Week 3)

**CANONICALIZE tests** ✅ (7 tests total):
- ✅ Many hypotheses (5 hypotheses, 120 permutations, <10ms)
- ✅ Identical hypotheses (duplicates)
- ✅ Idempotence: canon(canon(s)) = canon(s)
- ✅ α-equivalence preservation
- ✅ Logical meaning preservation (mutual inclusion)
- ✅ Simple axiom (no hypotheses)
- ✅ Single hypothesis

**Method**: Write tests, verify with `cargo +1.77 test --all-features`

### 2.4 Property-Based Tests ✅ EXCELLENT EXISTING COVERAGE

**Status**: 12 comprehensive property tests already exist and passing

**Tool**: proptest (already in dev-dependencies, pinned to 1.5.0 for Rust 1.77)

**Existing Coverage** ✅:

**Unification** (tests/unification_properties.rs):
- ✅ Idempotence: unify(t, t) succeeds with identity
- ✅ Symmetry (modulo renaming)
- ✅ Substitution correctness: unify(t1, t2) = σ ⟹ t1σ = t2σ
- ✅ Type safety, structural compatibility

**Substitution**:
- ✅ Composition: (σ ∘ τ)(t) = σ(τ(t))
- ✅ Identity: id(t) = t
- ✅ No cycles (occurs check)

**Statement** (3 property tests added in Week 2):
- ✅ Canonical idempotence
- ✅ α-equivalence preservation
- ✅ Logical meaning preservation (mutual inclusion)

**Optional Future Work** ⏸ (Week 4):
- Additional Statement operation properties (nice to have, not required for v0.1.0)

### 2.5 Boolean Evaluation Tests ✅ GOOD EXISTING COVERAGE

**Status**: Comprehensive tests already exist

**Existing Coverage** ✅ (tests/bool_eval/tests.rs):
- ✅ All 16 truth functions (2 variables)
- ✅ Truth functions with 3+ variables (u8, u16, u32, u64, u128)
- ✅ With bigint feature (>7 variables)
- ✅ Tautology detection
- ✅ Specific operations (AND, OR, XOR, etc.)
- ✅ 100+ Principia Mathematica proofs validated as tautologies

**Optional Future Work** ⏸:
- Systematic coverage of all truth functions (future enhancement)

### 2.6 Distinctness Graph Tests ✅ ADEQUATE EXISTING COVERAGE

**Status**: Basic coverage exists, adequate for v0.1.0

**Existing Coverage** ✅:
- ✅ Graph operations tested via Statement operations
- ✅ Distinctness constraints tested in APPLY regression test
- ✅ Basic functionality verified

**Optional Future Work** ⏸:
- Comprehensive standalone graph tests (future enhancement)

---

## Phase 3: API Review for Database Compatibility

### 3.1 Copy vs Clone Audit

**Verify no Copy constraints**:
```bash
grep -r "Copy" src/ --include="*.rs" | grep -i "trait"
```

**Check**:
- Type trait doesn't require Copy
- Term trait doesn't require Copy
- Node trait doesn't require Copy
- Metavariable trait doesn't require Copy
- Statement doesn't require Copy

**Deliverable**: Confirmation or fixes

### 3.2 Trait Object Safety

**Test compilation**:
```rust
// Must compile with Rust 1.77
let _: Arc<dyn Type> = todo!();
let _: Arc<dyn Node> = todo!();
let _: Arc<dyn Metavariable> = todo!();
```

**Method**:
```bash
cargo +1.77 check --all-features
```

### 3.3 Feature Compatibility Check

**Verify no Rust >1.77 features used**:

Common issues to check:
- `let-else` syntax (added 1.65, ok)
- `if let` guards (added 1.65, ok)
- `async fn` in traits (added 1.75, ok)
- Lazy cell types (stabilized 1.80, NOT OK - use OnceLock from 1.70)

**Method**: Compile with 1.77, review any errors

---

## Success Criteria

### Documentation
- FormalSpec.md matches implementation
- All public traits fully documented
- All public functions have examples
- Examples compile with Rust 1.77

### Testing
- Test coverage >80% for core modules
- All edge cases covered
- Property tests passing
- All tests pass with Rust 1.77

### API
- Compatible with Arc-based database integration
- No Copy requirements blocking Arc
- Trait objects work
- No Rust >1.77 features used

---

## Execution Checklist

### Before Starting
- [x] `rustup install 1.77.0`
- [x] Verify: `cargo +1.77 --version` shows 1.77.0

### Documentation Phase ✅ COMPLETED
- [x] Audit FormalSpec.md vs implementation
- [x] Check trait documentation
- [x] Verify all examples compile with 1.77
- [x] Review academic accessibility
- **Findings**: Documented in AUDIT_FINDINGS.md

### Testing Phase ✅ WEEK 1-3 COMPLETE
- [x] Run existing tests with `cargo +1.77 test --all-features`
- [x] Identify coverage gaps (documented in PHASE2_TEST_COVERAGE.md)
- [ ] Add unification edge case tests (some exist, needs review)
- [x] Add statement operation edge case tests (27 tests added total)
  - [x] CONTRACT error cases (4 tests)
  - [x] CONTRACT edge cases (2 tests)
  - [x] APPLY error cases (2 tests)
  - [x] APPLY success cases (2 tests)
  - [x] APPLY_MULTIPLE error cases (3 tests)
  - [x] APPLY_MULTIPLE success cases (1 test)
  - [x] CONDENSED_DETACH error cases (2 tests)
  - [x] CONDENSED_DETACH success cases (2 tests)
  - [x] CANONICALIZE property tests (3 tests)
  - [x] CANONICALIZE edge cases (4 tests)
  - [x] CONTRACT success cases (2 tests)
- [ ] Add property-based tests (Week 4 - optional)
- [ ] Add Boolean evaluation tests (future work)
- [ ] Add distinctness graph tests (future work)
- [x] Verify all pass with 1.77 (117/117 tests passing)

### API Review Phase ⏸ NOT STARTED
- [ ] Copy vs Clone audit
- [ ] Trait object safety check
- [ ] Feature compatibility check with 1.77
- [ ] Verify no >1.77 stdlib usage

### Final Verification ✅ COMPLETE
- [x] `cargo +1.77 build --all-features` (passes)
- [x] `cargo +1.77 test --all-features` (117 tests pass)
- [x] `cargo +1.77 clippy --all-features --all-targets` (no warnings)
- [x] `cargo +1.77 doc --all-features` (builds cleanly)
- [x] `cargo +1.77 fmt --check` (all formatted correctly)
- [x] All pass without warnings

---

## Notes on Generated Code

### src/bool_eval/generated_enum.rs

This file contains ~50+ TODO comments for naming 3-variable Boolean operations. These are **documentation TODOs only** and do not affect functionality.

**Important**: This file is entirely generated by `src/bool_eval/generate_boolean_ops.py`. Any changes to the TODOs must be made in the Python generator script, not in the generated Rust code.

**Status**: ⏸ Optional future work (better naming for generated operations)

---

## Findings Template

For each issue:
```
**Issue**: [Description]
**Location**: file.rs:line
**Severity**: Critical / Important / Minor
**Fix**: [Proposed solution]
**MSRV Impact**: Does fix require >1.77? Yes/No
```

---

## Audit Complete

All critical phases (1 & 2) complete. Project is ready for v0.1.0 release.

**Next Steps** (Optional):
- Phase 3: API Review (for future database compatibility)
- Week 4 testing (additional property tests)
- Python generator improvements (better naming for 3-variable Boolean ops)
