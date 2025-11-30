#!/bin/bash
set -e

LLVM_COV=~/.rustup/toolchains/nightly-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/bin/llvm-cov

echo "Finding all test binaries..."
TEST_BINARIES=$(find target/debug/deps -type f -perm +111 -name 'symbolic_mgu-*' | grep -v '\.d$')

echo "Test binaries found:"
echo "$TEST_BINARIES"

echo ""
echo "Generating HTML coverage report..."

# Build --object flags for all binaries
OBJECT_FLAGS=""
for binary in $TEST_BINARIES; do
    OBJECT_FLAGS="$OBJECT_FLAGS --object $binary"
done

$LLVM_COV show \
  --format=html \
  --output-dir=htmlcov \
  --show-line-counts-or-regions \
  --ignore-filename-regex='/.cargo/registry' \
  --instr-profile=lib_coverage.profdata \
  $OBJECT_FLAGS

echo ""
echo "Coverage report generated in htmlcov/"
