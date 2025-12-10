# Post-Release TODO (After v0.1.0)

## Semantic Versioning Enforcement

### Set Up cargo-semver-checks

Once v0.1.0 is published to crates.io, we should add automated semver checking to prevent accidental breaking changes.

#### Installation

```bash
cargo install cargo-semver-checks
```

#### Local Usage

```bash
# Check if current changes break semver relative to published version
cargo semver-checks check-release

# Or compare against specific version
cargo semver-checks check-release --baseline-version 0.1.0
```

#### CI Integration

Add `.github/workflows/semver.yml`:

```yaml
name: Semver Check

on:
  pull_request:
  push:
    branches: [main, v010]

jobs:
  semver:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: Install cargo-semver-checks
        run: cargo install cargo-semver-checks --locked
      - name: Check for breaking changes
        run: |
          # Only check if we have a published version
          if cargo search symbolic-mgu --limit 1 | grep -q symbolic-mgu; then
            cargo semver-checks check-release
          else
            echo "No published version found, skipping semver check"
          fi
```

#### Pre-commit Hook (Optional)

Add to `.git/hooks/pre-commit`:

```bash
#!/bin/bash
# Check for semver violations before commit

if command -v cargo-semver-checks &> /dev/null; then
    echo "Checking for semver violations..."
    cargo semver-checks check-release || {
        echo "WARNING: Semver violation detected!"
        echo "Breaking changes require version bump (0.x.y → 0.(x+1).0)"
        exit 1
    }
fi
```

### API Baseline Tracking (Alternative/Supplementary)

Use `cargo-public-api` to track API surface:

```bash
# Install
cargo install cargo-public-api

# Generate baseline after v0.1.0 release
cargo +nightly public-api > tests/api-baseline-v0.1.0.txt

# Check for changes
cargo +nightly public-api diff tests/api-baseline-v0.1.0.txt
```

Commit baselines to version control:
- `tests/api-baseline-v0.1.0.txt`
- `tests/api-baseline-v0.2.0.txt`
- etc.

## Other Post-Release Tasks

### Crates.io Badge

Add to README.md:

```markdown
[![Crates.io](https://img.shields.io/crates/v/symbolic-mgu.svg)](https://crates.io/crates/symbolic-mgu)
[![Documentation](https://docs.rs/symbolic-mgu/badge.svg)](https://docs.rs/symbolic-mgu)
[![License](https://img.shields.io/crates/l/symbolic-mgu.svg)](LICENSE)
```

### docs.rs Configuration

Ensure `.cargo/config.toml` has:

```toml
[build]
rustdocflags = ["--cfg", "doc"]
```

And `Cargo.toml` has:

```toml
[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "doc"]
```

### Release Checklist

For each release after v0.1.0:

1. Run `cargo semver-checks check-release`
2. Update CHANGELOG.md
3. Bump version in Cargo.toml
4. Run all quality gates (clippy, doc, test)
5. Tag release: `git tag v0.x.y`
6. Push tags: `git push --tags`
7. Publish: `cargo publish`
8. Create GitHub release with notes
9. Update API baseline if needed

## Timeline

Execute these tasks **after v0.1.0 is published** to crates.io.

## References

- [cargo-semver-checks documentation](https://crates.io/crates/cargo-semver-checks)
- [cargo-public-api documentation](https://crates.io/crates/cargo-public-api)
- [Semantic Versioning 2.0.0](https://semver.org/)
- [Rust API Guidelines - Compatibility](https://rust-lang.github.io/api-guidelines/compatibility.html)
