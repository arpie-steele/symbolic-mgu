# symbolic-mgu

[![Crates.io Version](https://img.shields.io/crates/v/symbolic-mgu)](https://crates.io/crates/symbolic-mgu)
[![docs.rs](https://img.shields.io/docsrs/symbolic-mgu)](https://docs.rs/symbolic-mgu/latest/symbolic_mgu/)
![Crates.io License](https://img.shields.io/crates/l/symbolic-mgu)
![Crates.io Downloads](https://img.shields.io/crates/d/symbolic-mgu)


A Rust library for symbolic logic unification using Most General Unifiers (MGU).

## Overview

symbolic-mgu provides a framework for representing logical formulas as structured
objects and applying unification operations for automated theorem proving.
The implementation follows Robinson's unification algorithm and supports
Meredith's condensed detachment principle.

**Academic Context:** This crate implements typed symbolic unification based on Robinson (1965) and Meredith's condensed detachment (1953). For detailed mathematical background, references, and citation information, see [docs/SCHOLARLY_CONTEXT.md](docs/SCHOLARLY_CONTEXT.md).

### Key Features

**Core Unification:**
- Robinson's unification algorithm with occurs check
- Type-safe substitutions (prevents cycles like x ↦ f(x))
- Type-aware matching (Boolean, Setvar, Class hierarchy)
- Normal form maintenance (no variable chains)

**Theorem Proving:**
- Statement operations: SUBSTITUTE, APPLY, CONTRACT
- Meredith's condensed detachment for propositional logic
- Distinctness graphs to prevent invalid substitutions

**Boolean Expression Evaluation:**
- Truth table generation for formulas with up to 7+ variables
- Support for arbitrary variable counts with `bigint` feature
- Efficient bit-wise operations on compact representations

## Quick Start

### Building and Testing

```bash
# Build the library
cargo build

# Run all tests
cargo test

# Build with all features (including bigint for 7+ variables)
cargo build --all-features

# Build and view documentation
cargo doc --open
```

### Usage Example

The library provides trait-based abstractions for terms, substitutions, and unification:

```rust
use symbolic_mgu::{unify, Substitution, EnumTerm, MetaByte, NodeByte, SimpleType};

// Create terms representing logical formulas
// Unify terms to find most general unifiers
// Apply substitutions to derive new theorems
```

See the [full API documentation](https://docs.rs/symbolic-mgu) for detailed usage.

## Documentation

- **API Reference**: Full documentation embedded in source code, available via `cargo doc`
- **Mathematical Specification**: See `src/FormalSpec.md` for formal definitions
- **System Overview**: See `src/SystemOverview.md` for architecture
- **Boolean Operations**: See `src/NodeBytesLogicTable.md` for operation reference

## Optional Features

- **`bigint`**: Support for Boolean logic with more than 7 variables (requires `num-bigint`)
- **`serde`**: JSON serialization support for terms and statements

### Building with Features

```bash
# Build with all features
cargo build --all-features

# Build with specific features
cargo build --features bigint,serde
```

## Minimum Rust Version

This crate requires Rust 1.77 or later and uses edition 2018 for maximum compatibility.

## Citation

If you use symbolic-mgu in published research, please cite it as:

> *symbolic-mgu (v0.1.x)* — a Rust library for typed symbolic unification and condensed detachment.
> Available at [crates.io/crates/symbolic-mgu](https://crates.io/crates/symbolic-mgu).

For foundational references (Robinson 1965, Meredith 1953, etc.), see [docs/SCHOLARLY_CONTEXT.md](docs/SCHOLARLY_CONTEXT.md).

