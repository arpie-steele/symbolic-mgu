# Plan: Addressing Statement Operations Test Gaps

**Date**: 2025-11-15
**Goal**: Add comprehensive tests for Statement operations before v0.1.0
**Strategy**: Start with error cases (easy), then edge cases, then success cases (hard)

---

## Philosophy: Error Cases Before Success Cases

**Key Insight**: Testing that operations *fail correctly* is easier than testing they *succeed correctly*, because:
- Error cases don't require mathematical validity - just proper error handling
- Success cases require knowing the correct result - which is mathematically non-trivial
- We can leverage existing worked examples (compact proofs, PM database) for success validation

**Approach**:
1. **Error cases** (easiest): Verify operations reject invalid inputs correctly
2. **Edge cases** (medium): Boundary conditions, empty structures
3. **Success cases** (hardest): Leverage existing proofs and simple hand-crafted examples
4. **Property tests** (if applicable): Algebraic laws, idempotence, etc.

---

## Priority Order

### Phase A: CONTRACT Tests (Highest Priority - Completely Untested)
### Phase B: CANONICALIZE Tests (High Priority - Expensive, No Validation)
### Phase C: APPLY Tests (Medium Priority - Expand Beyond Single Regression Test)
### Phase D: APPLY_MULTIPLE Tests (Medium Priority - Used by condensed_detach)
### Phase E: CONDENSED_DETACH Tests (Lower Priority - Has Indirect Coverage)
### Phase F: Property Tests (Nice to Have - Algebraic Properties)

---

## Phase A: CONTRACT Tests

**Operation**: `contract(factory, n, m)` - Unify two hypotheses within a statement
**Location**: `src/statement/operations.rs:47-90`
**Current Tests**: 0

### A1. Error Cases (Easiest - Start Here) ✅

These test that CONTRACT properly rejects invalid inputs:

#### A1.1: Invalid Indices
```rust
#[test]
fn contract_with_equal_indices_fails() {
    // contract(stmt, 0, 0) should error: can't contract with self
}

#[test]
fn contract_with_out_of_bounds_n_fails() {
    // contract(stmt, 99, 0) should error: index out of range
}

#[test]
fn contract_with_out_of_bounds_m_fails() {
    // contract(stmt, 0, 99) should error: index out of range
}
```

**Difficulty**: ⭐ (Very Easy)
**Approach**: Create simple statement, call with bad indices, verify MguError

#### A1.2: Unification Failures
```rust
#[test]
fn contract_incompatible_types_fails() {
    // Hypothesis 0: Boolean variable φ
    // Hypothesis 1: Setvar variable x
    // contract(stmt, 0, 1) should error: Boolean ⊥ Setvar
}

#[test]
fn contract_different_operators_fails() {
    // Hypothesis 0: P → Q
    // Hypothesis 1: P ∧ Q
    // contract(stmt, 0, 1) should error: Implies ≠ And
}

#[test]
fn contract_occurs_check_fails() {
    // Hypothesis 0: φ
    // Hypothesis 1: ¬φ
    // contract(stmt, 0, 1) should error: occurs check
    // Actually, this might succeed! Need to think about this.
}
```

**Difficulty**: ⭐⭐ (Easy)
**Approach**: Create statements with intentionally incompatible hypotheses

#### A1.3: Distinctness Violations
```rust
#[test]
fn contract_violates_distinctness_constraint() {
    // Assertion: x ∈ y → ...
    // Hypothesis 0: φ (Boolean var)
    // Hypothesis 1: ψ (Boolean var)
    // Distinctness: x ≠ y
    //
    // If unifying φ with (x ∈ y) would map both x and y to same tree,
    // that violates distinctness.
    //
    // This is tricky - may need a concrete example from FormalSpec.md
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Study FormalSpec.md distinctness examples, create minimal case

### A2. Success Cases - Simple (Medium Difficulty)

#### A2.1: Identical Hypotheses
```rust
#[test]
fn contract_identical_hypotheses_succeeds() {
    // Assertion: φ
    // Hypothesis 0: P
    // Hypothesis 1: P
    // Distinctness: {}
    //
    // contract(stmt, 0, 1) should:
    // - Unify with identity substitution (P ↦ P)
    // - Result: (φ; [P]; {})
    // - Only one copy of P in hypotheses
}
```

**Difficulty**: ⭐⭐ (Easy)
**Approach**: Create, verify hypothesis count reduces

#### A2.2: Unifiable Variables
```rust
#[test]
fn contract_unifies_variables() {
    // Assertion: φ → ψ
    // Hypothesis 0: φ
    // Hypothesis 1: ψ
    // Distinctness: {}
    //
    // contract(stmt, 0, 1) should succeed
    // Result assertion: χ → χ (both renamed to same variable)
    // Result hypotheses: [χ]
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Create, verify substitution applied correctly

### A3. Edge Cases (Medium Difficulty)

#### A3.1: Empty Distinctness Graph
```rust
#[test]
fn contract_with_empty_distinctness_graph() {
    // Most common case - no distinctness constraints
    // Should succeed for any unifiable hypotheses
}
```

**Difficulty**: ⭐⭐ (Easy)

#### A3.2: Substitution Creates Duplicate Hypotheses
```rust
#[test]
fn contract_produces_additional_duplicates() {
    // Assertion: φ → ψ
    // Hypothesis 0: φ
    // Hypothesis 1: ψ
    // Hypothesis 2: φ  (duplicate of H0, but not being contracted)
    //
    // contract(stmt, 0, 1) unifies φ with ψ, creating substitution σ = {φ ↦ χ, ψ ↦ χ}
    // After σ applied:
    // - Hypothesis 0: χ
    // - Hypothesis 1: χ
    // - Hypothesis 2: χ
    // All three are now identical, should be deduplicated to single χ
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Verify deduplication works correctly

### A4. Success Cases - Complex (Hardest)

#### A4.1: From Existing Compact Proofs
```rust
#[test]
fn contract_validates_against_known_proof_step() {
    // Mine compact proofs for cases where CONTRACT would be used
    // Use from_compact_proof to create statement, verify operation succeeds
    //
    // This leverages worked examples rather than inventing new ones
}
```

**Difficulty**: ⭐⭐⭐⭐ (Hard - requires analysis)
**Approach**: Analyze compact proof strings to identify CONTRACT-like operations

---

## Phase B: CANONICALIZE Tests

**Operation**: `canonicalize(var_factory, term_factory)` - Produce canonical form
**Location**: `src/statement/operations.rs:508-685`
**Current Tests**: 0
**Critical**: This is an expensive (factorial) operation with NO correctness validation

### B1. Property Tests (Easiest for Canonicalize)

These verify the algebraic properties canonicalization MUST satisfy:

#### B1.1: Idempotence
```rust
#[test]
fn canonicalize_is_idempotent() {
    // For any statement S:
    // canon(canon(S)) = canon(S)
    //
    // Create arbitrary statement, canonicalize twice, verify equal
}
```

**Difficulty**: ⭐⭐ (Easy)
**Approach**: Create statement, call canonicalize twice, use is_identical() to verify

#### B1.2: Preserves α-Equivalence
```rust
#[test]
fn canonicalize_preserves_alpha_equivalence() {
    // If S1 and S2 are identical (mutually include each other),
    // then canon(S1) = canon(S2)
    //
    // Create two α-equivalent statements (same structure, different var names)
    // Canonicalize both, verify they're equal
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Create renamed copies, canonicalize, compare

#### B1.3: Preserves Logical Meaning
```rust
#[test]
fn canonicalize_preserves_inclusion() {
    // For any statement S:
    // S and canon(S) are identical (mutually include each other)
    //
    // Create statement, canonicalize, verify is_identical(S, canon(S))
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Use existing is_identical() method

### B2. Edge Cases

#### B2.1: Simple Axiom (No Hypotheses)
```rust
#[test]
fn canonicalize_simple_axiom() {
    // Statement with no hypotheses - only assertion to normalize
    // Example: φ₅ → φ₂ should become φ₀ → φ₁
}
```

**Difficulty**: ⭐⭐ (Easy)
**Approach**: Hand-craft, verify variable renumbering

#### B2.2: Single Hypothesis
```rust
#[test]
fn canonicalize_single_hypothesis() {
    // No permutations to try (factorial(1) = 1)
    // Only variable renumbering
}
```

**Difficulty**: ⭐⭐ (Easy)

#### B2.3: Many Hypotheses (Performance Check)
```rust
#[test]
fn canonicalize_with_many_hypotheses() {
    // 5+ hypotheses (factorial(5) = 120 permutations)
    // This is a performance test - should complete in reasonable time
    // May want to mark as #[ignore] for normal test runs
}
```

**Difficulty**: ⭐⭐ (Easy)
**Purpose**: Verify doesn't hang or take excessive time

#### B2.4: Identical Hypotheses
```rust
#[test]
fn canonicalize_with_duplicate_hypotheses() {
    // Hypotheses: [P, Q, P]
    // Multiple permutations yield same result
    // Verify handles correctly
}
```

**Difficulty**: ⭐⭐ (Easy)

### B3. Success Cases - Verification

#### B3.1: Known Canonical Forms
```rust
#[test]
fn canonicalize_produces_expected_form() {
    // Use examples from FormalSpec.md or documentation
    // Example from operations.rs:535-548 (φ₂ → φ₅ becomes φ₀ → φ₁)
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Use doc examples as test cases

---

## Phase C: APPLY Tests

**Operation**: `apply(var_factory, term_factory, n, other)` - Unify hypothesis with assertion
**Location**: `src/statement/operations.rs:217-299`
**Current Tests**: 1 regression test (disjointness)

### C1. Error Cases (Build on Existing Regression Test)

#### C1.1: Invalid Index
```rust
#[test]
fn apply_with_out_of_bounds_index_fails() {
    // apply(stmt, 99, other) should error
}
```

**Difficulty**: ⭐ (Very Easy)

#### C1.2: Type Mismatch
```rust
#[test]
fn apply_type_mismatch_fails() {
    // S1.hypothesis[0]: Boolean variable
    // S2.assertion: Setvar variable
    // apply(S1, 0, S2) should error: Boolean ⊥ Setvar
}
```

**Difficulty**: ⭐⭐ (Easy)

#### C1.3: Distinctness Violation
```rust
#[test]
fn apply_violates_distinctness() {
    // This is more complex - need concrete example
    // Similar to contract distinctness violation
}
```

**Difficulty**: ⭐⭐⭐ (Medium)

### C2. Success Cases - Simple

#### C2.1: Apply Simple Axiom (Existing Pattern)
```rust
#[test]
fn apply_simple_axiom_to_modus_ponens() {
    // This is what regression test does - expand it
    // Modus Ponens: (φ → ψ; [φ → ψ, φ]; {})
    // Simp: (φ → (ψ → φ); []; {})
    //
    // apply(MP, 0, Simp) should consume first hypothesis
}
```

**Difficulty**: ⭐⭐ (Easy - pattern exists)
**Approach**: Expand existing regression_compact_proofs.rs test

#### C2.2: Consume All Hypotheses
```rust
#[test]
fn apply_consumes_all_hypotheses() {
    // Statement with 1 hypothesis
    // Apply statement that satisfies it
    // Result should have 0 hypotheses (theorem)
}
```

**Difficulty**: ⭐⭐⭐ (Medium)

### C3. Edge Cases

#### C3.1: No Hypotheses in Target
```rust
#[test]
fn apply_to_statement_with_no_hypotheses() {
    // S1: (A; []; {}) - simple axiom
    // Cannot apply anything (no hypotheses to satisfy)
    // Should this error or be allowed? Check implementation.
}
```

**Difficulty**: ⭐⭐ (Easy - exploratory)

#### C3.2: Variable Collision Handling
```rust
#[test]
fn apply_handles_variable_collision() {
    // This is what the regression test validates
    // Both statements use same variable names
    // Verify relabel_disjoint is called correctly
}
```

**Difficulty**: ⭐⭐ (Easy - expand existing test)

---

## Phase D: APPLY_MULTIPLE Tests

**Operation**: `apply_multiple(var_factory, term_factory, proofs)` - Satisfy multiple hypotheses
**Location**: `src/statement/operations.rs:301-465`
**Current Tests**: 0
**Used By**: condensed_detach (line 502)

### D1. Error Cases

#### D1.1: Empty Proofs List
```rust
#[test]
fn apply_multiple_with_empty_proofs_fails() {
    // Statement with 2 hypotheses, proofs = []
    // Should error: insufficient proofs
}
```

**Difficulty**: ⭐ (Very Easy)

#### D1.2: Too Few Proofs
```rust
#[test]
fn apply_multiple_with_too_few_proofs_fails() {
    // Statement with 3 hypotheses, proofs.len() = 2
    // Should error: insufficient proofs
}
```

**Difficulty**: ⭐ (Very Easy)

#### D1.3: Too Many Proofs
```rust
#[test]
fn apply_multiple_with_too_many_proofs_fails() {
    // Statement with 2 hypotheses, proofs.len() = 3
    // Should error or ignore extras? Check implementation.
}
```

**Difficulty**: ⭐ (Very Easy - exploratory)

### D2. Success Cases - Leverage condensed_detach

#### D2.1: Two Proofs (Modus Ponens Pattern)
```rust
#[test]
fn apply_multiple_modus_ponens() {
    // This is what condensed_detach does internally
    // Modus Ponens: 2 hypotheses
    // Provide 2 proofs
    // Verify both hypotheses satisfied
}
```

**Difficulty**: ⭐⭐⭐ (Medium)
**Approach**: Extract pattern from condensed_detach implementation

---

## Phase E: CONDENSED_DETACH Tests

**Operation**: `condensed_detach(var_factory, term_factory, minor, major)` - Modus ponens
**Location**: `src/statement/operations.rs:467-506`
**Current Tests**: 0 direct (extensive indirect via compact proofs)
**Note**: This has the BEST indirect coverage via PM proofs

### E1. Error Cases

#### E1.1: Major Premise Not Implication
```rust
#[test]
fn condensed_detach_non_implication_major_fails() {
    // Major premise: P ∧ Q (not an implication)
    // Should error: major premise must be implication
}
```

**Difficulty**: ⭐⭐ (Easy)

#### E1.2: Premises Don't Match
```rust
#[test]
fn condensed_detach_non_matching_premises_fails() {
    // Major: P → Q
    // Minor: R (doesn't unify with P)
    // Should error: minor premise doesn't match antecedent
}
```

**Difficulty**: ⭐⭐ (Easy)

### E2. Success Cases - Leverage Existing Proofs

#### E2.1: Classic Modus Ponens
```rust
#[test]
fn condensed_detach_classic_modus_ponens() {
    // Major: P → Q
    // Minor: P
    // Result: Q
    //
    // This is the simplest case from logic textbooks
}
```

**Difficulty**: ⭐⭐⭐ (Medium)

#### E2.2: Validate Against Compact Proof
```rust
#[test]
fn condensed_detach_matches_compact_proof() {
    // Take a simple compact proof like "DD211"
    // Manually construct equivalent using condensed_detach
    // Verify results are identical
}
```

**Difficulty**: ⭐⭐⭐⭐ (Hard)
**Approach**: Reverse-engineer compact proof steps

---

## Phase F: Property Tests

These test algebraic properties that SHOULD hold (but may reveal bugs):

### F1. Canonicalize Properties (Covered in Phase B)

### F2. CONTRACT Properties

```rust
proptest! {
    #[test]
    fn contract_preserves_validity(stmt in arbitrary_valid_statement()) {
        // If S is valid and contract(S, n, m) succeeds,
        // then result is also valid
        if let Ok(result) = stmt.contract(...) {
            prop_assert!(result.is_valid());
        }
    }
}
```

**Difficulty**: ⭐⭐⭐⭐ (Hard - need arbitrary_valid_statement generator)

### F3. Inclusion Properties

```rust
#[test]
fn inclusion_is_transitive() {
    // If S1 ⊇ S2 and S2 ⊇ S3, then S1 ⊇ S3
    // This may already be tested in inclusion.rs
}
```

**Difficulty**: ⭐⭐⭐ (Medium)

---

## Implementation Strategy

### Week 1: Low-Hanging Fruit (Error Cases)
- [ ] A1: CONTRACT error cases (6 tests) - ⭐/⭐⭐
- [ ] C1: APPLY error cases (3 tests) - ⭐/⭐⭐
- [ ] D1: APPLY_MULTIPLE error cases (3 tests) - ⭐
- [ ] E1: CONDENSED_DETACH error cases (2 tests) - ⭐⭐

**Total**: ~14 tests, all difficulty ⭐-⭐⭐
**Goal**: Verify error handling is correct

### Week 2: Canonicalize Properties & Simple Success Cases
- [ ] B1: CANONICALIZE property tests (3 tests) - ⭐⭐/⭐⭐⭐
- [ ] B2: CANONICALIZE edge cases (4 tests) - ⭐⭐
- [ ] A2: CONTRACT simple success cases (2 tests) - ⭐⭐/⭐⭐⭐

**Total**: ~9 tests, difficulty ⭐⭐-⭐⭐⭐
**Goal**: Validate most critical operation (CANONICALIZE) properties

### Week 3: Expand Coverage
- [ ] A3: CONTRACT edge cases (2 tests) - ⭐⭐⭐
- [ ] C2: APPLY simple success cases (2 tests) - ⭐⭐/⭐⭐⭐
- [ ] D2: APPLY_MULTIPLE success cases (1 test) - ⭐⭐⭐
- [ ] E2: CONDENSED_DETACH success cases (2 tests) - ⭐⭐⭐/⭐⭐⭐⭐

**Total**: ~7 tests, difficulty ⭐⭐⭐-⭐⭐⭐⭐
**Goal**: Cover main success paths

### Week 4: Complex Cases (If Time/Interest)
- [ ] A4: CONTRACT from compact proofs - ⭐⭐⭐⭐
- [ ] B3: CANONICALIZE verification - ⭐⭐⭐
- [ ] F: Property tests - ⭐⭐⭐⭐

**Total**: ~3-5 tests, difficulty ⭐⭐⭐-⭐⭐⭐⭐
**Goal**: Comprehensive coverage

---

## Success Criteria

**Minimum (v0.1.0 Release)**:
- ✅ All error cases tested (~14 tests)
- ✅ CANONICALIZE properties verified (~7 tests)
- ✅ Basic success cases for each operation (~5 tests)
- **Total**: ~26 tests minimum

**Good Coverage**:
- Above minimum +
- ✅ All edge cases (~8 tests)
- ✅ Most success cases (~10 tests)
- **Total**: ~44 tests

**Comprehensive**:
- Above good +
- ✅ Property tests (~3 tests)
- ✅ Complex validation against proofs (~3 tests)
- **Total**: ~50 tests

---

## Notes on Difficulty

**Why Error Cases Are Easier**:
- Don't need to know correct answer, just that it errors
- MguError variants are well-defined
- Can create obviously invalid inputs

**Why Success Cases Are Harder**:
- Need to verify CORRECTNESS, not just non-failure
- Requires understanding mathematical validity
- May need to hand-calculate expected results

**Why Property Tests Are Hardest**:
- Need to generate arbitrary valid statements (non-trivial)
- Properties must hold for ALL inputs
- Requires deep understanding of algebraic laws

**Strategy**: Start easy, build confidence, tackle hard problems last.
