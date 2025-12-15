# Metamath-exe Test Files

This directory contains test files from the official metamath-exe repository:
https://github.com/metamath/metamath-exe/tree/master/tests

## File Organization

Test files include both positive tests (valid Metamath files) and negative tests (files that should fail parsing).

### Negative Test Naming
Files with `-bad` suffixes are negative tests that should fail with specific errors:
- `*-bad1.mm`, `*-bad2.mm`, etc. - Different error conditions for the same feature

### Positive Tests
Files without `-bad` suffixes are valid Metamath files that should parse successfully.

### File Inclusion Tests
- `demo0-includer.mm` - Tests `$[` `$]` file inclusion
- `demo0-includee.mm` - Included by `demo0-includer.mm`

## Usage

These test files are used to verify the parser implementation matches the behavior of the reference metamath-exe C implementation.

## Downloaded
Date: 2025-12-11
Count: 32 files
Source: https://github.com/metamath/metamath-exe @ master branch
