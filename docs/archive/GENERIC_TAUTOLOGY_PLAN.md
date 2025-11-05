# Generic Tautology Function Refactoring Plan

## Goal
Refactor `test_tautology()` from working only with `EnumTerm<Ty, V, No>` to accepting any type implementing `Term<Ty, V, No>`.

## Current State

**File**: `src/bool_eval/mod.rs` (lines 573-670)

**Current signature**:
```rust
pub fn test_tautology<Ty, V, No>(term: &EnumTerm<Ty, V, No>) -> Result<bool, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    No: Node<Type = Ty> + TryInto<NodeByte>,
    <No as TryInto<NodeByte>>::Error: Into<MguError>,
```

**Problem**: Hardcoded to `EnumTerm`, limiting reusability with other Term implementations (e.g., database-backed terms, cached terms, etc.)

## Proposed Solution

### New Signature
```rust
pub fn test_tautology<T, Ty, V, No>(term: &T) -> Result<bool, MguError>
where
    T: Term<Ty, V, No>,
    Ty: Type,
    V: Metavariable<Type = Ty>,
    No: Node<Type = Ty> + TryInto<NodeByte>,
    <No as TryInto<NodeByte>>::Error: Into<MguError>,
```

**Key change**: Add generic parameter `T: Term<Ty, V, No>` instead of hardcoding `EnumTerm<Ty, V, No>`

### Why This Works

The `Term` trait is defined as:
```rust
pub trait Term<T, V, N>: Debug + Display + PartialEq + Eq + Hash + Clone
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
```

And has these associated types:
- `type Type: Type;`
- `type Metavariable: Metavariable;`
- `type Node: Node;`

For `EnumTerm`, these are implemented as:
```rust
impl<Ty, V, N> Term<Ty, V, N> for EnumTerm<Ty, V, N> {
    type Type = Ty;
    type Metavariable = V;
    type Node = N;
}
```

**Important**: The Term trait uses both generic parameters AND associated types. The generic parameters make the impl unique, while associated types provide convenient access. For our refactoring, we work with the generic parameters.

## Implementation Changes

### What Stays the Same

The implementation already uses trait methods, so no changes needed for:

1. **Metavariable collection** (line 582):
   ```rust
   term.collect_metavariables(&mut vars_set)?;  // Already a trait method
   ```

2. **Type checking** (line 590):
   ```rust
   var.get_type()?  // Already a trait method on Metavariable
   ```

3. **Evaluation calls** (lines 622-661):
   ```rust
   <u8 as UnsignedBits<u8, 3>>::eval_boolean_term::<Ty, V, No, _>(term, &vars)?;
   ```
   These calls work with any `&T where T: Term<Ty, V, No>` because `eval_boolean_term` accepts a generic term.

### What Changes

**Only the function signature** - change from:
```rust
term: &EnumTerm<Ty, V, No>
```

To:
```rust
term: &T
```

And add `T: Term<Ty, V, No>` to the where clause.

## Benefits

1. **Flexibility**: Works with any Term implementation:
   - `EnumTerm<Ty, V, No>` (current use case)
   - Database-backed terms
   - Cached/memoized terms
   - Future term implementations

2. **Architecture alignment**: Matches the project's principle of "trait abstractions first"

3. **Zero runtime cost**: Generic functions are monomorphized at compile time

4. **Backward compatibility**: All existing tests continue to work unchanged

## Testing Strategy

**No new tests needed** - existing tests already provide full coverage:
- `tautology_simple()` - Tests `p ∨ ¬p`
- `tautology_not_tautology()` - Tests `p ∧ ¬p`
- `tautology_de_morgan()` - Tests De Morgan's law

These tests construct `EnumTerm` instances, which implement `Term<SimpleType, MetaByte, NodeByte>`, so they'll continue to work with the generic signature.

**Future tests** could verify the function works with other Term implementations if/when they're added.

## Documentation Updates

### Function Documentation (lines 544-572)
Update the example from:
```rust
/// let p = EnumTerm::build_metavariable(SimpleType::Boolean, 0)?;
/// let not_p = EnumTerm::build_node(SimpleType::Boolean, NodeByte::Not, &[p.clone()])?;
/// let law = EnumTerm::build_node(SimpleType::Boolean, NodeByte::Or, &[p, not_p])?;
```

To emphasize genericity:
```rust
/// // Works with any Term implementation, e.g., EnumTerm:
/// let p = EnumTerm::Leaf(MetaByte::try_from_type_and_index(SimpleType::Boolean, 0)?);
/// let not_p = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p.clone()]);
/// let law = EnumTerm::NodeOrLeaf(NodeByte::Or, vec![p, not_p]);
```

### BOOL_EVAL_BACKPORT_PLAN.md
Add a new section documenting this enhancement:

```markdown
### Phase 4: Generic Term Support ✅ COMPLETE

**Completed enhancement**:
- ✅ Refactored `test_tautology()` to accept any `T: Term<Ty, V, No>`
- ✅ Removed hardcoded dependency on `EnumTerm`
- ✅ Updated function documentation to emphasize genericity
- ✅ Verified all existing tests pass unchanged

**Benefits**:
- Works with any Term implementation (EnumTerm, DbTerm, etc.)
- Aligns with project principle: "trait abstractions first"
- Zero breaking changes - backward compatible
```

## Quality Gates

Before marking complete, verify:
- ✅ `cargo +1.77 check --all-features` - No compilation errors
- ✅ `cargo +1.77 test --all-features` - All 24 tests pass
- ✅ `cargo +1.77 clippy --all-features --all-targets` - No warnings
- ✅ `cargo +1.77 doc --all-features` - Documentation builds

## Implementation Steps

1. **Edit function signature** (line 573):
   - Change parameter from `term: &EnumTerm<Ty, V, No>` to `term: &T`
   - Add `T: Term<Ty, V, No>,` to where clause

2. **Update documentation** (lines 563-572):
   - Update example to emphasize generic usage
   - Note that any Term implementation works

3. **Run quality gates**:
   - Check compilation
   - Run tests
   - Run clippy
   - Build docs

4. **Update BOOL_EVAL_BACKPORT_PLAN.md**:
   - Add Phase 4 section documenting the enhancement

## Risk Assessment

**Risk level**: **VERY LOW**

**Why**:
- Change is purely mechanical (signature only)
- Implementation already uses trait methods throughout
- No behavioral changes
- Existing tests provide full verification
- Rust's type system guarantees correctness at compile time

## Estimated Time

**Total**: 15-20 minutes
- Edit code: 2 minutes
- Run quality gates: 5-10 minutes
- Update documentation: 5-8 minutes

---

## Future Enhancement: Support for BooleanSimpleNode<Ty>

### Motivation

The current `test_tautology()` requires `No: Node<Type = Ty> + TryInto<NodeByte>`, which works well for `SimpleType`-based systems where `NodeByte` is the standard node type.

However, users working with **exotic math tied to Booleans** may have custom Type and Node implementations that:
- Don't use `SimpleType` (might use custom type hierarchies)
- Can't convert to `NodeByte` (which is tied to `SimpleType`)
- Can convert to `BooleanSimpleNode<Ty>` (the generic wrapper around `BooleanSimpleOp`)

### Proposed Alternative Entry Point

```rust
/// Test if a Boolean term is a tautology (generic node variant).
///
/// This variant works with any Node type that can convert to `BooleanSimpleNode<Ty>`,
/// making it suitable for custom type systems with exotic Boolean operations.
///
/// For standard use cases with `SimpleType` and `NodeByte`, prefer [`test_tautology()`]
/// which has simpler trait bounds.
pub fn test_tautology_with_generic_nodes<T, Ty, V, No>(term: &T) -> Result<bool, MguError>
where
    T: Term<Ty, V, No>,
    Ty: Type,
    V: Metavariable<Type = Ty>,
    No: Node<Type = Ty> + TryInto<BooleanSimpleNode<Ty>>,
    <No as TryInto<BooleanSimpleNode<Ty>>>::Error: Into<MguError>,
{
    // Implementation would be similar to test_tautology() but use
    // BooleanSimpleNode<Ty> instead of NodeByte
    todo!("Future enhancement")
}
```

### Use Cases

1. **Custom Type Systems**: Projects using domain-specific type hierarchies (e.g., quantum logic, fuzzy logic, modal logic) that still have Boolean sub-systems

2. **Extended Mathematical Frameworks**: Systems with `OrdinalClass`, `ComplexNumberClass`, etc., as mentioned in CLAUDE.md, where Boolean operations exist within a richer type system

3. **Multi-Paradigm Systems**: Hybrid systems combining different logical frameworks, each with their own node types

4. **Database-Backed Nodes**: Custom node implementations backed by theorem databases that can interpret operations as Boolean but don't use the standard `NodeByte` encoding

### Implementation Notes

The implementation would:
1. Accept `No: TryInto<BooleanSimpleNode<Ty>>` instead of `No: TryInto<NodeByte>`
2. Convert nodes to `BooleanSimpleNode<Ty>` during evaluation
3. Use the same automatic type selection strategy (bool, u8, u16, ..., BigUint)
4. Share the same variable counting and Boolean type checking logic

### Why Two Entry Points?

Having both `test_tautology()` and `test_tautology_with_generic_nodes()` provides:

1. **Simplicity for common cases**: Most users work with `SimpleType` and `NodeByte`, so the simpler signature is more approachable

2. **Flexibility for advanced cases**: Users with custom type systems get a clear path to tautology testing without hacking around the `NodeByte` requirement

3. **Clear documentation**: Each function documents its intended use case

4. **Type system guidance**: Compiler errors naturally guide users to the right function based on their trait implementations

### Priority

**Phase 5** (Future Work) - Not blocking for v0.1.0-alpha.7

This enhancement should be added when:
- A user reports needing it for a custom type system, OR
- The project adds example custom Type implementations (e.g., `ExtendedType` with mathematical domains), OR
- Someone is working on database-backed theorem proving and needs more flexible node types

### Estimated Effort

**2-3 hours**:
- 1 hour: Implement the function (mostly copy-paste with trait bound changes)
- 1 hour: Add tests with a custom Type/Node implementation
- 30 minutes: Documentation and examples
- 30 minutes: Quality gates and review

---

## Appendix: Understanding Term Trait Design

The `Term` trait uses both generic parameters and associated types:

```rust
pub trait Term<T, V, N>: ...
where
    T: Type,
    V: Metavariable<Type = T>,
    N: Node<Type = T>,
{
    type Type: Type;
    type Metavariable: Metavariable;
    type Node: Node;
    // ...
}
```

**Generic parameters** (`T, V, N`):
- Make the impl unique (can't have two impls with different type parameters)
- Used in function signatures accepting/returning terms
- Required when a function needs to constrain the exact types

**Associated types** (`Type`, `Metavariable`, `Node`):
- Provide convenient access without repeating type parameters
- Used primarily within trait method implementations

For `test_tautology()`, we use the generic parameters approach because:
1. We need to pass the concrete types to `UnsignedBits::eval_boolean_term()`
2. We need to constrain `No: TryInto<NodeByte>`
3. We want to be explicit about the type relationships

This is the correct design for a generic function over Terms.
