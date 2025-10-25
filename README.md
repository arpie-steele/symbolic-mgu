# symbolic-mgu

A Rust library for symbolic logic unification using Most General Unifiers (MGU).

## Overview

symbolic-mgu provides a framework for representing logical formulas as structured
objects and applying unification operations for automated theorem proving.
The implementation follows Robinson's unification algorithm and supports
Meredith's condensed detachment principle.

Key features:
- Type-safe representation of logical terms (Boolean, Set, Class)
- Unification algorithm with occurs checking
- Statement operations (CONTRACT, APPLY) for theorem derivation
- Automatic canonicalization for consistent variable naming
- Distinctness graphs to prevent invalid substitutions
- Multiple compact representations for efficiency

## Quick Start

Build and test:
    cargo build
    cargo test

Build and view documentation:
    cargo doc --open

Run examples:
    cargo run --bin demo_graph

## Documentation

Full API documentation is embedded in the source code and available via `cargo doc`.

For the formal mathematical specification, see src/FormalSpec.md.

## Optional Features

- `bigint`: Support for testing logic for more than just 7 Boolean variables
- `serde`: JSON serialization support (stable Rust)

Build with features:

    cargo build --features bigint,serde

