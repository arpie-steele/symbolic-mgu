# Prioritized Remaining Work Items

**Date**: 2025-11-19
**Context**: v0.1.0-alpha.13 development
**Current Status**: All critical work complete, v0.1.0 release-ready

---

## Priority Tier 1: CRITICAL for v0.1.0 Release

### ✅ ALL COMPLETE

No critical blockers remain. All quality gates passing.

---

## Priority Tier 2: HIGH - API Stability (Phase 3) ✅ COMPLETE

**Date Completed**: 2025-11-19
**Status**: All tasks complete, documented in `docs/PHASE3_API_REVIEW.md`

### 2.1 Copy vs Clone Audit ✅ COMPLETE
**Results**:
- ✅ Type trait: `Clone` (NOT Copy)
- ✅ Node trait: `Clone` (NOT Copy)
- ✅ Metavariable trait: `Clone` (NOT Copy)
- ✅ Term trait: `Clone` (NOT Copy)
- ✅ Statement struct: Uses `Clone` (NOT Copy)

**Issue Found & Fixed**: ParametricMetavariable had 7 `Copy` constraints
- **Changed**: `self.ty.into()` → `self.ty.clone().into()` (8 locations)
- **Benefit**: Future `DbType` with `Arc<Database>` will work without breaking changes
- **File**: `src/metavariable/parametric.rs`

### 2.2 Trait Object Safety Check ✅ COMPLETE
**Results**:
- ✅ **TypeCore IS dyn-safe** (intentional - for error messages)
  - Omits `Clone`, `Eq`, `Hash`, `Ord`
  - Used in `MguError` as `Box<dyn TypeCore>`
  - Bridge: `Type::to_boxed()` → `Box<dyn TypeCore>`
- ✅ **Type, Node, Metavariable, Term NOT dyn-safe** (intentional - for generics)
  - Require `Clone + Eq + Hash + Ord` for collections/canonicalization
  - Used as concrete type parameters in `Statement<Ty, V, N, T>`

**Tests Added**: 6 new tests documenting design
- `typecore_is_dyn_safe()` - Verifies trait object works ✅
- `type_is_not_dyn_safe()` - Documents intentional non-dyn-safety ✅
- `to_boxed_works()` - Verifies bridge function ✅
- Similar tests for Node, Metavariable, Term ✅

**Test Count**: 136 → 142 unit tests (+6)

### 2.3 MSRV Feature Compatibility ✅ COMPLETE
**Results**:
- ✅ No `LazyLock`/`LazyCell` - Uses `OnceLock` (1.70) correctly
- ✅ No `offset_of!` macro
- ✅ No unstable features (`#![feature]`)
- ✅ No async/await
- ✅ Const generics used correctly (valid in 1.77)
- ✅ All dependencies compatible with 1.77
- ✅ Proptest pinned to 1.5.0 (1.6+ requires 1.82)

**Automated checks passed**: All language features and stdlib APIs verified compatible

### 2.4 Verify No >1.77 stdlib Usage ✅ COMPLETE
**Results**:
- ✅ All tests compile and run on Rust 1.77.0
- ✅ No compiler warnings
- ✅ No clippy warnings
- ✅ Documentation builds successfully
- ✅ Code formatted correctly

**Quality Gates (All Passing)**:
```bash
cargo +1.77 test --all-features              # ✅ 142 unit + 96 doc = 238 tests
cargo +1.77 clippy --all-features --all-targets  # ✅ 0 warnings
cargo +1.77 doc --all-features               # ✅ Clean build
cargo +1.77 fmt --check                      # ✅ Formatted
```

---

## Priority Tier 3: MEDIUM - Test Coverage Enhancements

**Goal**: Increase confidence in edge cases
**Risk**: Low - Core functionality already well-tested
**Effort**: 2-3 days
**Recommendation**: **Post-v0.1.0** (not blockers)

### 3.1 Unification Edge Case Tests ⭐⭐
**Why**: Additional coverage beyond existing property tests
**Current**: Some edge cases exist, 12 property tests passing
**Effort**: 3-4 hours
**Priority**: Low - Property tests provide excellent coverage

**Potential additions**:
- [ ] Deeply nested terms (depth >5)
- [ ] Circular substitution attempts (occurs check edge cases)
- [ ] Empty substitution edge cases
- [ ] Maximum variable index boundaries (MetaByte limit)

**Status**: ⏸ Deferred - Existing coverage adequate for v0.1.0

---

### 3.2 Distinctness Constraint Tests ⭐⭐
**Why**: Comprehensive standalone graph tests
**Current**: Tested via APPLY regression test
**Effort**: 2-3 hours
**Priority**: Low - Adequate coverage exists

**Potential additions**:
- [ ] Empty graph operations
- [ ] Large graphs (performance)
- [ ] Merge operations
- [ ] Constraint violation detection

**Status**: ⏸ Deferred - Existing coverage adequate for v0.1.0

---

### 3.3 Boolean Evaluation Systematic Coverage ⭐⭐
**Why**: Cover all 16 two-variable truth functions systematically
**Current**: Good coverage including 100+ PM proofs validated
**Effort**: 2-3 hours
**Priority**: Low - Existing validation is strong

**Potential additions**:
- [ ] Systematic enumeration of all 2-var functions
- [ ] 3-variable truth table validation
- [ ] Performance benchmarks for large expressions

**Status**: ⏸ Deferred - Existing coverage excellent for v0.1.0

---

### 3.4 Property-Based Tests for Statement Operations ⭐⭐⭐
**Why**: Catch edge cases via randomized testing
**Current**: CONTRACT, CANONICALIZE have manual tests; 3 CANONICALIZE properties
**Effort**: 4-6 hours (complex - needs arbitrary statement generator)
**Priority**: Medium - Would catch unexpected issues

**Requires**:
- Arbitrary valid statement generator (non-trivial)
- Property: contract preserves validity
- Property: apply preserves validity
- Property: operations compose correctly

**Blocker**: Need `arbitrary_valid_statement()` generator
**Status**: ⏸ Deferred - Requires significant infrastructure (Week 4+ effort)

---

## Priority Tier 4: LOW - Documentation & Cleanup

**Goal**: Polish and maintainability
**Risk**: Very Low - No functional impact
**Effort**: 1-2 days
**Recommendation**: **Post-v0.1.0**

### 4.1 Type Trait Documentation Example ⭐
**Why**: Help advanced users understand custom type systems
**Current**: Trait well-documented, but no custom type example
**Effort**: 1-2 hours
**Priority**: Very Low - SimpleType is clear example

**Potential**:
- [ ] Add example of custom type system in trait docs
- [ ] Reference DbType (Metamath) as future real-world example
- [ ] Reference NothingButBooleans (historical notation) as minimal example

**Status**: ⏸ Optional - Not needed for v0.1.0

---

### 4.2 Boolean Operations Naming ⭐
**Why**: Better names for generated 3-variable operations
**Current**: ~50+ TODO comments in `src/bool_eval/generated_enum.rs`
**Effort**: 2-3 hours
**Priority**: Very Low - Documentation only, no functional impact

**Note**: Must update Python generator `src/bool_eval/generate_boolean_ops.py`

**Check**:
- [ ] Review TODO comments in generated_enum.rs
- [ ] Research standard names for 3-variable operations
- [ ] Update Python generator script
- [ ] Regenerate Rust code

**Status**: ⏸ Optional future work

---

### 4.3 Test Organization Cleanup ⭐
**Why**: Improve test discoverability
**Current**: Tests distributed across modules (good) and tests/ dir
**Effort**: 1-2 hours
**Priority**: Very Low - Current organization is fine

**Potential**:
- [ ] Group related tests with comments
- [ ] Add module-level test documentation
- [ ] Consider test organization in future

**Status**: ⏸ Optional

---

## Priority Tier 5: FUTURE - New Features

**Goal**: Expand capability
**Risk**: N/A - New features
**Effort**: Weeks to months
**Recommendation**: **Post-v0.1.0** (next release cycle)

### 5.1 Metamath Integration (Next Major Feature)
**Why**: Enable importing Metamath databases
**Effort**: 3-4 weeks
**Priority**: High for v0.2.0
**Status**: Documented in `docs/METAMATH_ARCHITECTURE_V2.md`

**See**: METAMATH_ARCHITECTURE_V2.md for complete plan

---

### 5.2 NothingButBooleans Type (Historical Notation)
**Why**: Support pure propositional calculus
**Effort**: 1-2 days
**Priority**: Medium for v0.2.0
**Status**: Design documented in CLAUDE.md

---

### 5.3 ParametricMetavariable Enhancement
**Why**: Families of variable names
**Effort**: 1-2 weeks
**Priority**: Low for v0.2.0
**Status**: Basic implementation exists, needs expansion

---

## Execution Recommendation

### ✅ Phase 3 Complete (2025-11-19)
All API review tasks complete. See `docs/PHASE3_API_REVIEW.md` for full details.

**Changes Made**:
- Removed Copy constraints from ParametricMetavariable (1 file)
- Added 6 dyn-safety documentation tests
- Test count: 136 → 142 unit tests
- All quality gates passing

**Result**: API is ready for future database integration without breaking changes.

### After v0.1.0 Release (Optional):
2. **Tier 3: Test Enhancements** (optional, 2-3 days)
   - As time permits, not blockers
3. **Tier 4: Documentation** (optional, 1-2 days)
   - Polish only
4. **Tier 5: New Features** (v0.2.0 planning)
   - Metamath integration
   - Historical notation support

---

## Risk Assessment

### High Risk (Do Now):
- **Phase 3 API Review**: Breaking changes expensive after release

### Medium Risk (Can Defer):
- None - All medium-risk items complete

### Low Risk (Optional):
- Additional test coverage (Tier 3)
- Documentation polish (Tier 4)
- New features (Tier 5)

---

## Decision Point ✅ RESOLVED

**Phase 3 API Review Complete** (2025-11-19)

**Results**:
- ✅ API stability verified
- ✅ Future database integration will work without breaking changes
- ✅ All quality gates passing
- ✅ 142 unit tests + 96 doc tests = 238 tests passing
- ✅ Zero warnings (clippy, compiler, doc)

**Recommendation**: ✅ **READY FOR v0.1.0 RELEASE**

No blockers remain. Optional Tier 3-5 work can be deferred to post-release.
