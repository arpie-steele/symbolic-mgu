# Documentation and Testing Audit Plan

**Date**: 2025-11-15
**Status**: Ready to execute
**MSRV**: Rust 1.77.0 - ALL testing must use this toolchain

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

## Phase 1: Documentation Audit

### 1.1 FormalSpec.md vs Implementation

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

**Deliverable**: Confirmation of alignment or list of mismatches

### 1.2 Trait Documentation Completeness

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

**Deliverable**: Documentation improvement list

### 1.3 Public API Examples

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

**Deliverable**: APIs needing examples

### 1.4 Academic Accessibility

**Files**: All `*.md` in `src/` and `docs/`

**Check**:
- Terminology appropriate for target audience (math historians, mathematicians, CS researchers)
- No unnecessary jargon
- Citations properly formatted
- Mathematical notation consistent

**Deliverable**: Accessibility improvements needed

---

## Phase 2: Testing Audit

### 2.1 Current Test Coverage

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

### 2.3 Edge Cases: Statement Operations

**CONTRACT tests needed**:
- Empty distinctness graph
- Violated distinctness constraint
- Duplicate hypotheses result
- Unification failure

**APPLY tests needed**:
- No hypotheses
- All hypotheses consumed
- Distinctness violation
- Metavariable collision

**Canonicalization tests needed**:
- Many hypotheses (permutations)
- Identical hypotheses
- Idempotence: canon(canon(s)) = canon(s)

**Method**: Write tests, verify with `cargo +1.77 test`

### 2.4 Property-Based Tests

**Tool**: proptest (already in dev-dependencies, pinned to 1.5.0 for Rust 1.77)

**Properties to test**:

**Unification**:
- Idempotence: unify(t, t) succeeds with identity
- Symmetry (modulo renaming)
- Substitution correctness: unify(t1, t2) = σ ⟹ t1σ = t2σ

**Substitution**:
- Composition: (σ ∘ τ)(t) = σ(τ(t))
- Identity: id(t) = t
- No cycles (occurs check)

**Statement**:
- Canonical idempotence
- Inclusion transitivity

**Method**:
```bash
cargo +1.77 test --all-features -- --nocapture proptest
```

### 2.5 Boolean Evaluation Tests

**Systematic coverage**:
- All 16 truth functions (2 variables)
- Truth functions with 3+ variables
- With bigint feature (>7 variables)
- Tautology detection
- Contradiction detection

**Method**: Add tests, run with `cargo +1.77 test --all-features`

### 2.6 Distinctness Graph Tests

**Coverage needed**:
- Empty graph
- Complete graph
- Isolated vertices
- Clique detection
- Substitution transformation
- Graph merging

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
- [ ] `rustup install 1.77.0`
- [ ] Verify: `cargo +1.77 --version` shows 1.77.0

### Documentation Phase
- [ ] Audit FormalSpec.md vs implementation
- [ ] Check trait documentation
- [ ] Verify all examples compile with 1.77
- [ ] Review academic accessibility

### Testing Phase
- [ ] Run existing tests with `cargo +1.77 test --all-features`
- [ ] Identify coverage gaps
- [ ] Add unification edge case tests
- [ ] Add statement operation edge case tests
- [ ] Add property-based tests
- [ ] Add Boolean evaluation tests
- [ ] Add distinctness graph tests
- [ ] Verify all pass with 1.77

### API Review Phase
- [ ] Copy vs Clone audit
- [ ] Trait object safety check
- [ ] Feature compatibility check with 1.77
- [ ] Verify no >1.77 stdlib usage

### Final Verification
- [ ] `cargo +1.77 build --all-features`
- [ ] `cargo +1.77 test --all-features`
- [ ] `cargo +1.77 clippy --all-features --all-targets`
- [ ] `cargo +1.77 doc --all-features`
- [ ] All pass without warnings

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

## Next Step

Begin Phase 1.1: Audit FormalSpec.md against implementation with Rust 1.77.
