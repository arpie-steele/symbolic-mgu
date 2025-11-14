# MguError Usage Audit

**Date**: 2025-11-14
**Purpose**: Audit MguError usage to replace UnknownError with specific types and favor constructor methods
**Priority**: HIGH (API stability - error types are part of public contract)

## Executive Summary

**Found**: 21 UnknownError usages + numerous direct instantiations that bypass constructor methods
**Impact**: Poor error diagnostics, harder debugging, potential API instability
**Effort**: ~3-4 hours to fix all issues

## Problem Categories

### 1. UnknownError with Numeric Codes (DEPRECATED PATTERN)

The codebase uses `UnknownError(code)` which is marked as deprecated in `src/error/base.rs:119`:
```rust
/// Catch-all error (deprecated - use specific error types instead).
#[error("Unknown Error with code = {0}.")]
UnknownError(usize), // code
```

This pattern provides no semantic information - just a numeric code that requires looking up in source.

### 2. Direct Instantiation Instead of Constructor Methods

Many locations use raw `MguError::VariantName(...)` instead of the provided constructor methods like:
- `MguError::from_found_and_expected_types()`
- `MguError::from_found_and_expected_unsigned()`
- `MguError::from_index_and_len()`

**Why this matters**: Constructor methods provide:
- Type safety and automatic conversions
- Consistent error construction patterns
- Easier refactoring if error structures change

## Detailed Findings

### Category A: UnknownError in bool_eval Module

**File**: `src/bool_eval/mod.rs`
**Count**: 9 instances

| Line | Code | Context | Recommended Fix |
|------|------|---------|-----------------|
| ~119 | `MguError::UnknownError(121)` | Arity mismatch in macro | `MguError::from_found_and_expected_unsigned(arity, expected)` |
| ~700 | `MguError::UnknownError(700)` | Boolean node conversion failed | `MguError::ArgumentError("NodeByte is not a Boolean operation".into())` |
| ~701 | `MguError::UnknownError(701)` | get_metavariable() returned None | `MguError::ArgumentError("Term is not a metavariable".into())` |
| ~702 | `MguError::UnknownError(702)` | Variable not in vars slice | `MguError::ArgumentError(format!("Variable {:?} not found in binding list", var))` |
| ~703 | `MguError::UnknownError(703)` | Arity mismatch | `MguError::from_found_and_expected_unsigned(actual, expected)` |
| ~704 | `MguError::UnknownError(704)` | get_node() returned None | `MguError::ArgumentError("Term is not a node".into())` |
| ~705 | `MguError::UnknownError(705)` | Too many variables (>20) | `MguError::ArgumentError(format!("Too many Boolean variables: {} (max 20 without bigint)", n))` |
| ~706 | `MguError::UnknownError(706)` | eval_boolean_node returned None | `MguError::ArgumentError("Failed to evaluate Boolean node".into())` |

**Notes**:
- These are all in Boolean evaluation paths
- Most represent argument validation failures → `ArgumentError`
- Arity mismatches should use `from_found_and_expected_unsigned()`

### Category B: UnknownError in node/node_byte/factory.rs

**File**: `src/node/node_byte/factory.rs`
**Count**: 10 instances (codes 4321-4331)

| Line | Code | Context | Recommended Fix |
|------|------|---------|-----------------|
| 73 | `from_error_code(4321)` | NodeByte::from_str failed | `MguError::ArgumentError(format!("Unknown node name: {}", name))` |
| 94 | `from_error_code(4322)` | Invalid nullary code | `MguError::ArgumentError(format!("Invalid Boolean code for arity 0: {:#x}", code))` |
| 98 | `from_error_code(4323)` | Invalid unary code | `MguError::ArgumentError(format!("Invalid Boolean code for arity 1: {:#x}", code))` |
| ~104 | `from_error_code(4324)` | Invalid binary code | `MguError::ArgumentError(format!("Invalid Boolean code for arity 2: {:#x}", code))` |
| ~109 | `from_error_code(4325)` | Invalid ternary code | `MguError::ArgumentError(format!("Invalid Boolean code for arity 3: {:#x}", code))` |
| ~113 | `from_error_code(4326)` | Unsupported arity | `MguError::ArgumentError(format!("Unsupported arity: {}", arity))` |
| ~128 | `from_error_code(4328)` | BigInt not enabled | `MguError::ArgumentError("BigInt feature required for codes > u16::MAX".into())` |
| ~129 | `from_error_code(4329)` | Code conversion failed | `MguError::NumericConversionError(format!("Code {} doesn't fit in u16", code))` |
| ~130 | `from_error_code(4330)` | BooleanSimpleOp conversion failed | `MguError::ArgumentError(format!("Code {:#x} is not a valid BooleanSimpleOp", code))` |
| ~131 | `from_error_code(4331)` | BigInt conversion failed | `MguError::NumericConversionError("Failed to convert BigUint to Boolean code".into())` |

**Notes**:
- All are argument validation failures in factory methods
- Should use `ArgumentError` or `NumericConversionError` (already has variant!)
- Clear descriptive messages will greatly improve debugging

### Category C: UnknownError in logic Module

**File**: `src/logic/mod.rs`
**Count**: 1 instance

| Line | Code | Context | Recommended Fix |
|------|------|---------|-----------------|
| ~line | `from_error_code(0x8001)` | Type doesn't support Boolean | `MguError::ArgumentError(format!("Type {:?} does not support Boolean capability", typ))` |

**Notes**: This is checking type capability - should be clear ArgumentError.

### Category D: Direct Instantiation Patterns

These bypass constructor methods and should be refactored:

#### D1: UnificationFailure String Construction

**Files**: `src/term/substitution.rs`, `src/statement/operations.rs`, `src/statement/compact_proof.rs`, `src/statement/base.rs`
**Pattern**: `MguError::UnificationFailure(format!(...))` or `MguError::UnificationFailure("...".to_string())`
**Count**: ~20 instances

**Assessment**: ✅ **ACCEPTABLE** - `UnificationFailure` has a message-based constructor:
```rust
MguError::from_err_type_and_message(MguErrorType::UnificationFailure, msg)
```

**However**: Direct instantiation with `format!()` is actually cleaner here. The constructor method is verbose.

**Recommendation**:
- **Keep current pattern** OR
- Add simpler constructor: `MguError::unification_failure(msg: impl Into<String>)`

#### D2: ArgumentError String Construction

**Files**: `src/statement/operations.rs`
**Pattern**: `MguError::ArgumentError(format!(...))` or `MguError::ArgumentError("...".to_string())`
**Count**: ~10 instances

**Assessment**: Same as D1 - has constructor but direct is cleaner.

**Recommendation**: Same as D1 - add simpler constructor.

#### D3: ChildIndexOutOfRange Direct Construction

**Files**: `src/term/substitution.rs`, `src/statement/operations.rs`
**Pattern**: `MguError::ChildIndexOutOfRange(index, len)`
**Count**: ~5 instances

**Current constructor**:
```rust
MguError::from_index_and_len(None, index, length)  // None = no type info
```

**Assessment**: ⚠️ **SHOULD USE CONSTRUCTOR** - provides type flexibility

**Recommendation**: Replace with `MguError::from_index_and_len(None, index, length)`

## Recommended New Constructor Methods

To make error construction more ergonomic, add these helpers to `src/error/base.rs`:

```rust
impl MguError {
    /// Simplified constructor for UnificationFailure.
    pub fn unification_failure(msg: impl Into<String>) -> Self {
        MguError::UnificationFailure(msg.into())
    }

    /// Simplified constructor for ArgumentError.
    pub fn argument_error(msg: impl Into<String>) -> Self {
        MguError::ArgumentError(msg.into())
    }

    /// Simplified constructor for VerificationFailure.
    pub fn verification_failure(msg: impl Into<String>) -> Self {
        MguError::VerificationFailure(msg.into())
    }

    /// Simplified constructor for DistinctnessViolation.
    pub fn distinctness_violation(msg: impl Into<String>) -> Self {
        MguError::DistinctnessViolation(msg.into())
    }

    /// Constructor for unsupported type capability.
    pub fn unsupported_type(capability: impl Into<String>) -> Self {
        MguError::ArgumentError(format!("Type does not support {} capability", capability.into()))
    }
}
```

## Implementation Plan

### Phase 1: High Priority (~2 hours)

Replace all UnknownError instances:

1. **bool_eval module** (9 instances) - Lines ~119, 700-706
   - Most → `ArgumentError` with descriptive messages
   - Arity mismatches → `from_found_and_expected_unsigned()`

2. **node_byte/factory module** (10 instances) - Lines 73-131
   - Invalid codes → `ArgumentError` with hex formatting
   - Numeric conversions → `NumericConversionError`
   - Missing feature → `ArgumentError("...feature required")`

3. **logic module** (1 instance) - Line with 0x8001
   - Type capability check → `ArgumentError` or new `unsupported_type()` helper

### Phase 2: Medium Priority (~1 hour)

Add simplified constructor methods:

1. Add to `src/error/base.rs`:
   - `unification_failure(msg)`
   - `argument_error(msg)`
   - `verification_failure(msg)`
   - `distinctness_violation(msg)`
   - `unsupported_type(capability)`

2. Update test in `src/error/base.rs:603` to test new constructors

### Phase 3: Low Priority (~1 hour)

Refactor `ChildIndexOutOfRange` direct instantiations:

1. **term/substitution.rs** - Replace ~3 instances
2. **statement/operations.rs** - Replace ~2 instances

Use: `MguError::from_index_and_len(None, index, length)`

### Phase 4: Documentation (30 min)

1. Update `MguError` module docs to show preferred constructor patterns
2. Add examples using new simplified constructors
3. Mark `from_error_code()` as deprecated (add `#[deprecated]` attribute)

## Testing Strategy

For each changed error site:

1. **Verify error message clarity**: Run existing tests and check error output
2. **Check error type**: Ensure `get_error_type()` returns correct variant
3. **Test error context**: Verify all contextual info is preserved

**Regression risk**: LOW - Error construction changes don't affect success paths

## API Impact Assessment

### Breaking Changes: NONE

All changes are internal error construction details. The error enum variants themselves don't change.

### Behavioral Changes: MINOR (Improvements)

- Error messages become more descriptive
- Error types become more specific (UnknownError → ArgumentError, etc.)
- Users matching on `MguError::UnknownError(_)` will see fewer matches (good!)

### Benefits for v0.1.0

1. **Clearer API contract**: Error types clearly indicate failure modes
2. **Better diagnostics**: Descriptive messages instead of numeric codes
3. **Future-proof**: Specific errors easier to evolve than catch-all UnknownError
4. **User experience**: Clearer error messages = easier debugging for library users

## Example Transformations

### Before:
```rust
// Unclear - what does 703 mean?
return Err(MguError::UnknownError(703));

// Verbose - constructor adds no value
return Err(MguError::from_err_type_and_message(
    MguErrorType::ArgumentError,
    format!("Variable {} not found", var)
));

// Direct instantiation - misses type flexibility
return Err(MguError::ChildIndexOutOfRange(i, n));
```

### After:
```rust
// Clear semantic meaning
return Err(MguError::argument_error(format!(
    "Term has {} children, expected {}",
    actual, expected
)));

// Clean and semantic
return Err(MguError::argument_error(format!(
    "Variable {} not found in binding list",
    var
)));

// Uses constructor - allows future type context addition
return Err(MguError::from_index_and_len(None, i, n));
```

## Completion Checklist

- [ ] Phase 1: Replace all UnknownError instances (21 total)
  - [ ] bool_eval/mod.rs (9 instances)
  - [ ] node/node_byte/factory.rs (10 instances)
  - [ ] logic/mod.rs (1 instance)
  - [ ] macros.rs (1 instance)
- [ ] Phase 2: Add simplified constructor methods (5 new methods)
  - [ ] Add methods to src/error/base.rs
  - [ ] Add tests for new constructors
- [ ] Phase 3: Refactor ChildIndexOutOfRange instantiations (5 instances)
  - [ ] term/substitution.rs
  - [ ] statement/operations.rs
- [ ] Phase 4: Documentation updates
  - [ ] Update module docs with examples
  - [ ] Deprecate `from_error_code()`
- [ ] Testing: Run full test suite
  - [ ] `cargo +1.77 test --all-features`
  - [ ] `cargo +1.77 clippy --all-features --all-targets`
  - [ ] `cargo +1.77 doc --all-features`

## Priority for alpha.12

**Recommendation**: ✅ **HIGH PRIORITY** - Phase 1 should be completed before v0.1.0

**Rationale**:
- Error types are part of public API
- Descriptive errors critical for user experience
- Low risk, high impact improvements
- Aligns with API stability goal (clear contracts)

**Time estimate**: 2-3 hours for Phase 1 (core improvements)

## Notes for Next Session

- All UnknownError locations catalogued with specific line numbers and context
- Constructor method recommendations based on error semantics, not just pattern matching
- Some direct instantiations (UnificationFailure, ArgumentError with format!()) are acceptable
- Focus on Phase 1 (UnknownError replacement) for immediate impact
- Phases 2-4 can be done incrementally post-alpha.12
