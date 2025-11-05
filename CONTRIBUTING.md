# Contributing to symbolic-mgu

Thank you for your interest in contributing! This document outlines the development practices and policies for this project.

## Getting Started

### Prerequisites

- **Rust**: Minimum version 1.77
- **Toolchain**: `cargo +1.77` for consistency
- **Edition**: 2018 (for maximum compatibility)

### Building

```bash
# Clone the repository
git clone https://github.com/YOUR_USERNAME/symbolic-mgu.git
cd symbolic-mgu

# Build the project
cargo +1.77 build --all-features

# Run tests
cargo +1.77 test --all-features

# Run clippy
cargo +1.77 clippy --all-features --all-targets

# Build documentation
cargo +1.77 doc --all-features
```

## Code Quality Gates

Before submitting a pull request, ensure all quality gates pass:

```bash
# 1. All tests must pass
cargo +1.77 test --all-features

# 2. No clippy warnings
cargo +1.77 clippy --all-features --all-targets

# 3. Documentation builds without warnings
cargo +1.77 doc --all-features

# 4. Code is formatted
cargo +1.77 fmt --check
```

## Code Style

### General Principles

- **Result over panic**: Strongly prefer `Result` types over panicking
- **Trait abstractions first**: Use trait abstractions over concrete types when possible
- **Factory pattern for primitives**: Node, Metavariable, and Term use factory patterns
- **No emojis**: Unless explicitly requested, avoid emojis in code and documentation

### Rust-Specific

- Follow the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- Use TODO comments instead of `println!` debugging
- Comprehensive documentation on public items (this project has extensive lint warnings enabled)
- Prefer iterators over manual loops where appropriate

### Documentation

All public items must be documented with:
- Summary line (one sentence, ending with period)
- Optional detailed explanation
- `# Examples` section for non-trivial functions
- `# Errors` section documenting failure modes
- `# Panics` section if panicking is possible

Example:
```rust
/// Computes the most general unifier of two terms.
///
/// Uses Robinson's unification algorithm with occurs check.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::{unify, Term};
///
/// let t1 = term_factory.create_var(0);
/// let t2 = term_factory.create_var(1);
/// let mgu = unify(&t1, &t2).unwrap();
/// ```
///
/// # Errors
///
/// Returns [`MguError::UnificationFailure`] if the terms cannot be unified.
pub fn unify<T: Term>(t1: &T, t2: &T) -> Result<Substitution<T>, MguError> {
    // ...
}
```

## Semantic Versioning Policy

This library follows [Semantic Versioning 2.0.0](https://semver.org/).

### Pre-1.0 (0.x.y) - Current

- **Breaking changes** → minor version bump (0.1.0 → 0.2.0)
- **New features** → minor version bump (0.1.0 → 0.2.0)
- **Bug fixes only** → patch version bump (0.1.0 → 0.1.1)

### Post-1.0 (x.y.z) - Future

- **Breaking changes** → major version bump (1.0.0 → 2.0.0)
- **New features** → minor version bump (1.0.0 → 1.1.0)
- **Bug fixes** → patch version bump (1.0.0 → 1.0.1)

### What Counts as Breaking?

The following changes are considered **breaking** and require appropriate version bumps:

#### API Changes
- ❌ Changing public function/method signatures
- ❌ Adding non-default methods to public traits
- ❌ Removing public items (functions, types, modules)
- ❌ Renaming public items
- ❌ Changing error types returned by public functions

#### Type Changes
- ❌ Adding private fields to public structs
- ❌ Removing public fields from structs
- ❌ Changing field types in public structs
- ❌ Making pub structs `#[non_exhaustive]` when they weren't before

#### Behavior Changes
- ❌ Changing documented behavior (even if fixing a bug)
- ❌ Increasing MSRV (Minimum Supported Rust Version)

### What Is NOT Breaking?

The following are generally safe to do in minor/patch releases:

#### Additions (0.x: minor, 1.x: minor)
- ✅ Adding new public functions, types, traits
- ✅ Adding new methods with default implementations to traits
- ✅ Adding private fields to `#[non_exhaustive]` structs
- ✅ Adding trait implementations for existing types

#### Internal Changes (0.x: patch, 1.x: patch)
- ✅ Refactoring internal implementation
- ✅ Performance improvements
- ✅ Fixing bugs without behavior changes
- ✅ Improving documentation
- ✅ Improving error messages

### Compatibility Strategy

To avoid breaking changes when extending functionality:

1. **Extension Traits** - Add new methods via extension traits:
   ```rust
   // Instead of adding to existing trait:
   pub trait NewFeature {
       fn new_method(&self) -> Result<T, E>;
   }

   // Blanket impl for existing types:
   impl<T: ExistingTrait> NewFeature for T { ... }
   ```

2. **Builder Pattern** - Use builders for complex construction:
   ```rust
   // Can add fields without breaking existing usage:
   MyStruct::builder()
       .field1(value1)
       .field2(value2)
       .build()
   ```

3. **TryInto/TryFrom** - For format conversions:
   ```rust
   // When adding new output formats, use TryInto
   // to build compatibility wrappers from existing support:
   impl TryFrom<AsciiFormatter> for NewFormatter { ... }
   ```

4. **Feature Flags** - Gate experimental APIs:
   ```rust
   #[cfg(feature = "experimental")]
   pub fn experimental_feature() { ... }
   ```

### Enforcement

After v0.1.0 is published, we will use [`cargo-semver-checks`](https://crates.io/crates/cargo-semver-checks) in CI to automatically detect breaking changes. See `docs/POST_RELEASE_TODO.md` for setup instructions.

## Testing

### Test Requirements

- All new features must include tests
- Bug fixes should include regression tests
- Tests should be clear and well-documented
- Use descriptive test names: `test_unification_with_occurs_check_fails`

### Test Organization

- **Unit tests**: In the same file as the code using `#[cfg(test)] mod tests`
- **Integration tests**: In `tests/` directory for cross-module testing
- **Doc tests**: Examples in documentation that are automatically tested

### Running Specific Tests

```bash
# Run all tests
cargo +1.77 test --all-features

# Run specific test
cargo +1.77 test test_name

# Run tests for specific module
cargo +1.77 test --test module_name

# Run doctests only
cargo +1.77 test --doc
```

## Architecture Guidelines

See `TODO.md` and the `docs/` directory for detailed architectural principles and design documents. Key points:

### Factory Pattern

Use factories for **primitives** (Node, Metavariable, Term), not composites (Statement):
- ✅ Factories: Support different construction strategies
- ✅ Traits: Define behavior, not construction
- ❌ Don't use factories for types assembled from primitives

### Type System Flexibility

The `Type` trait enables different type systems:
- Capability-based: Types can opt-in to Boolean/Setvar/Class
- Extensible: New types (OrdinalClass, RealNumberClass) possible
- Backward compatible: Existing `SimpleType` enum implements the trait

### Math Correctness First

Proving mathematical correctness always takes priority over auxiliary features.

## Commit Message Guidelines

We don't enforce a strict format, but good commit messages help:

```
Brief summary (50 chars or less)

More detailed explanation if needed. Explain what and why,
not how (the code shows how).

- Bullet points are fine
- Reference issues: Fixes #123
- Break lines at 72 characters
```

## Pull Request Process

1. Fork the repository and create a branch
2. Make your changes, following code style guidelines
3. Add tests for new functionality
4. Ensure all quality gates pass
5. Update documentation as needed
6. Submit pull request with clear description

### PR Checklist

- [ ] All tests pass (`cargo +1.77 test --all-features`)
- [ ] No clippy warnings (`cargo +1.77 clippy --all-features --all-targets`)
- [ ] Documentation builds (`cargo +1.77 doc --all-features`)
- [ ] Code is formatted (`cargo +1.77 fmt`)
- [ ] New features have tests
- [ ] Public items are documented
- [ ] Breaking changes are noted (if any)

## Dependency Policy

Be conservative with package additions:
- Prefer stdlib over external crates when possible (e.g., `OnceLock` over `lazy_static`)
- Choose packages with long-term support and community backing
- Avoid packages with sole maintainers when alternatives exist
- Optional features should use optional dependencies

Example: `bigint` feature is opt-in because not all use cases need >6 Boolean variables.

## Getting Help

- **Documentation**: See `docs/` directory for design documents
- **Planning**: Check `TODO.md` for roadmap and implementation details
- **Questions**: Open a discussion on GitHub
- **Bugs**: Open an issue with minimal reproduction

## License

By contributing, you agree that your contributions will be licensed under the same terms as the project (see LICENSE file).

## Code of Conduct

Be respectful and constructive. We're here to advance mathematical logic and theorem proving tools.
