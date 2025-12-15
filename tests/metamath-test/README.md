# Metamath-test Test Files

This directory contains test files from David A. Wheeler's metamath-test repository:
https://github.com/david-a-wheeler/metamath-test

## About This Repository

The [metamath-test repository](https://github.com/david-a-wheeler/metamath-test) is a test suite for Metamath proof verifier implementations. It provides a "bake-off" comparison between different Metamath parsers and verifiers.

## Files Included

This directory contains **unique** test files not already present in metamath-exe:

- `emptyline.mm` - Tests handling of empty lines
- `hol.mm` - Higher-order logic database
- `iset.mm` - Intuitionistic set theory
- `miu.mm` - MIU formal system (from Hofstadter's GEB)
- `nf.mm` - Tests related to proper substitution
- `peano-fixed.mm` - Peano arithmetic formalization
- `ql.mm` - Quantum logic
- `set-dist-bad1.mm` - Negative test for set theory
- `set.2010-08-29.mm` - Snapshot of set.mm (historical)
- `set.mm` - Current version of set.mm (large database, 40K+ theorems)

## Overlap with metamath-exe

Many files overlap with the metamath-exe tests. Those duplicates are in `../metamath-exe/` and not duplicated here.

## Usage

These provide additional coverage beyond metamath-exe tests, particularly:
- Different logical systems (hol, iset, ql)
- Historical snapshots (set.2010-08-29.mm)
- Current full database (set.mm)

## License

Repository is MIT licensed. Individual test files have various licenses (many CC0).

## Downloaded
Date: 2025-12-11
Count: 9 unique files
Source: https://github.com/david-a-wheeler/metamath-test @ master branch
