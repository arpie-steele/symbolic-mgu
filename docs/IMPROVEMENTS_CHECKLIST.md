# Code and Test Improvements Checklist

This document tracks potential improvements to code quality, testing, and documentation that are not part of the main v0.1.0 roadmap in `TODO.md`. These items can be addressed opportunistically or deferred to future releases.

## Documentation Enhancements

### WideMetavariable Module
- [ ] Add module-level usage examples showing ASCII_* constants with `WideMetavariableFactory`
- [ ] Document the subscript calculation formula: `subscript = index / n_chars`
- [ ] Add explicit cross-references from ASCII_* constants to `docs/PARAMETRIC_METAVARIABLE_DESIGN.md`
- [ ] Document character selection rationale (why these specific Greek letters, why this ordering)
- [ ] Add examples showing how to interpret subscripted variables (φ₁₂ means what index?)

### Architecture Documentation
- [ ] Document which public APIs are "sealed" (won't be extended) vs "open" (may grow in future)
- [ ] Add decision records for major architectural choices (why factory pattern, why trait-first)
- [ ] Create migration guide template for users upgrading between 0.x versions

### API Documentation
- [ ] Ensure all public items have `# Examples` sections (audit with `cargo +1.77 doc --all-features`)
- [ ] Add `# Performance` sections to methods with non-trivial complexity
- [ ] Document panic conditions comprehensively (audit usage of `unwrap()`, `expect()`, array indexing)

## Testing Improvements

### Property-Based Tests
- [ ] Verify `ASCII_BOOLEANS.len() == OUR_BOOLEANS.chars().count()` at compile time
- [ ] Verify `ASCII_SETVARS.len() == OUR_SETVARS.chars().count()` at compile time
- [ ] Verify `ASCII_CLASSES.len() == OUR_CLASSES.chars().count()` at compile time
- [ ] Property test: Each ASCII string maps to correct UTF-8 char by index position
- [ ] Property test: `WideMetavariable` round-trip: `try_from_type_and_index` → `get_type_and_index` preserves values
- [ ] Property test: Subscript calculation is consistent and invertible

### Integration Tests
- [ ] Test `WideMetavariable` with compact binary on proof requiring >256 distinct variables
- [ ] Test interoperability: convert between `MetaByte`, `AsciiMetaVar`, and `WideMetavariable` representations
- [ ] Test long proof chains with variable renaming (stress test `WideMetavariableFactory`)
- [ ] Test edge cases: proofs with exactly 32, 33, 64, 65 variables (boundary conditions)

### Edge Case Tests
- [ ] Test `WideMetavariable` display with very large subscripts (index = 1000, 10000)
- [ ] Test all 12 Boolean characters display correctly with subscripts 0-20
- [ ] Test all 26 Setvar characters with subscripts, including PLANCK CONSTANT (ℎ) edge case
- [ ] Test all 26 Class characters with subscripts
- [ ] Test error conditions: invalid type codes, out-of-range indices

### Performance Tests
- [ ] Benchmark: `MetaByte` vs `WideMetavariable` variable allocation
- [ ] Benchmark: `MetaByte` vs `WideMetavariable` display formatting
- [ ] Benchmark: Proof generation with 10/100/1000 variables
- [ ] Profile: Memory usage of `WideMetavariableFactory` with different cache strategies

### Regression Tests
- [ ] Add test cases for any bugs discovered during development
- [ ] Create minimal reproduction cases for subtle unification edge cases
- [ ] Test cases from Metamath set.mm database (once integration is implemented)

## Code Quality Improvements

### WideMetavariable Module
- [ ] Consider making `ASCII_*` constants public once formatter system uses them (remove `#[allow(dead_code)]`)
- [ ] Add helper function: `ascii_for_index(Type, usize) -> Option<&'static str>` for formatter use
- [ ] Extract character mapping tables to separate module if they grow (currently manageable)
- [ ] Add compile-time assertions for character count consistency (when `const_panic` stabilizes)

### Error Handling
- [ ] Audit all `unwrap()` calls: should they be `expect()` with context or proper `Result` propagation?
- [ ] Review `expect()` messages: are they actionable and informative?
- [ ] Consider adding error context with `thiserror` or similar (if not already using)
- [ ] Ensure all public functions document error conditions in `# Errors` sections

### Type Safety
- [ ] Consider newtype wrappers for indices: `struct BooleanIndex(usize)` vs raw `usize`
- [ ] Review use of `usize` for metavariable counts: should there be a maximum limit type?
- [ ] Consider `#[non_exhaustive]` on enums/structs that may need extension
- [ ] Audit public struct fields: should any be private with accessors?

### Code Organization
- [ ] Consider extracting ASCII mapping constants to `src/metavariable/ascii_mappings.rs`
- [ ] Review module visibility: are all `pub(crate)` items truly internal?
- [ ] Check for code duplication between `MetaByte` and `WideMetavariable` implementations
- [ ] Consider shared trait for ASCII representation if pattern repeats

## Future Compatibility

### Semantic Versioning Preparation
- [ ] Audit public API surface: what might need to change before v1.0?
- [ ] Document provisional APIs with clear warnings in docstrings
- [ ] Consider feature flags for experimental functionality
- [ ] Plan extension points: where should users expect to add custom implementations?

### Formatter System Integration (Phase 7.10)
- [ ] Design how `ASCII_*` constants will be used by formatters
- [ ] Plan backward compatibility if formatter interface changes
- [ ] Consider `format_with()` method signatures for `WideMetavariable`
- [ ] Document formatter trait requirements in advance

### ParametricMetavariable Migration
- [ ] Plan migration path from `WideMetavariable` to `ParametricMetavariable`
- [ ] Ensure tests cover both implementations during transition
- [ ] Document what will change for users of `WideMetavariable` API
- [ ] Consider deprecation warnings if `WideMetavariable` will be removed

## CI/Automation (Post v0.1.0 Release)

These items should be addressed after v0.1.0 is published to crates.io, per `docs/POST_RELEASE_TODO.md`:

- [ ] Set up `cargo-semver-checks` in GitHub Actions
- [ ] Add API baseline generation to release workflow
- [ ] Create pre-commit hook template in `scripts/pre-commit.sh`
- [ ] Add crates.io and docs.rs badges to README.md
- [ ] Set up automated changelog generation
- [ ] Consider cargo-audit for dependency security checking

## Tooling and Developer Experience

### Build System
- [ ] Add `Makefile` or `justfile` with common commands
- [ ] Document Rust 1.77 installation for contributors
- [ ] Provide `rustup override` setup instructions
- [ ] Consider `.cargo/config.toml` with common flags

### Editor Support
- [ ] Add `.editorconfig` for consistent formatting
- [ ] Provide VSCode workspace settings template
- [ ] Document Rust Analyzer configuration recommendations
- [ ] Add clippy configuration if project-specific lints needed

### Scripts and Helpers
- [ ] Create `scripts/check.sh` that runs all quality gates
- [ ] Create `scripts/test-all.sh` for comprehensive test suite
- [ ] Consider `scripts/benchmark.sh` for performance tracking
- [ ] Add `scripts/generate-docs.sh` for local doc preview

## Documentation Website (Future)

When project is more mature:

- [ ] Consider mdBook or similar for comprehensive documentation
- [ ] Tutorial: "Your First Condensed Detachment Proof"
- [ ] Guide: "Understanding Unification Algorithms"
- [ ] Reference: "Complete API Guide with Examples"
- [ ] Comparison with other logic libraries

## Community and Contribution

- [ ] Add CONTRIBUTORS.md acknowledging contributions
- [ ] Create issue templates for bugs and feature requests
- [ ] Add pull request template with checklist
- [ ] Consider GitHub Discussions for Q&A
- [ ] Add examples/ directory with real-world usage

---

## Priority Guidelines

**High Priority** (should address before v0.1.0):
- Property tests for ASCII mapping consistency
- Document panic conditions in public APIs
- Audit error handling (unwrap/expect)

**Medium Priority** (v0.1.1 or v0.2.0):
- Performance benchmarks
- Integration tests with long proofs
- Code organization improvements

**Low Priority** (future releases):
- Developer tooling enhancements
- Documentation website
- Community infrastructure

---

## References

- Main roadmap: `TODO.md`
- Post-release automation: `docs/POST_RELEASE_TODO.md`
- Contribution guidelines: `CONTRIBUTING.md`
- Formatter design: `docs/FORMATTER_DESIGN.md`
- ParametricMetavariable design: `docs/PARAMETRIC_METAVARIABLE_DESIGN.md`
