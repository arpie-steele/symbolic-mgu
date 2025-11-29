#!/bin/bash
set -e  # Exit on error

# Verify nightly toolchain is available
if ! rustup toolchain list | grep -q nightly; then
    echo "Error: nightly toolchain not installed"
    echo "Run: rustup toolchain install nightly"
    exit 1
fi

# Find LLVM tools in nightly toolchain sysroot (portable across architectures)
SYSROOT=$(rustc +nightly --print sysroot)
TARGET=$(rustc -vV | grep host | cut -d' ' -f2)
LLVM_TOOLS="$SYSROOT/lib/rustlib/$TARGET/bin"
LLVM_PROFDATA="$LLVM_TOOLS/llvm-profdata"
LLVM_COV="$LLVM_TOOLS/llvm-cov"

# Verify LLVM tools exist
if [ ! -x "$LLVM_PROFDATA" ]; then
    echo "Error: llvm-profdata not found at $LLVM_PROFDATA"
    echo "Run: rustup component add llvm-tools-preview --toolchain nightly"
    exit 1
fi

# Clean everything for fresh coverage run
echo "Cleaning build artifacts and old coverage data..."
cargo clean
rm -f *.profraw *.profdata
rm -rf htmlcov

# Define feature combinations to test
# default=[] so no need for --no-default-features
declare -a FEATURE_SETS=(
    "no-features:"
    "bigint:--features bigint"
    "serde:--features serde"
    "all-features:--all-features"
)

# Run tests for each feature combination
for feature_spec in "${FEATURE_SETS[@]}"; do
    IFS=':' read -r name flags <<< "$feature_spec"
    echo ""
    echo "========================================="
    echo "Running tests with: $name"
    echo "========================================="

    RUSTFLAGS="-C instrument-coverage" \
        cargo +nightly test $flags -- --include-ignored

    if [ $name = no-features -o $name = all-features ] ; then

        RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly run $flags --bin compact

        RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly run $flags --bin compact -- KoreHaNanDesuKa

        RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly run $flags --bin compact -- --help

        RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly run $flags --bin compact \
            -- \
            D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

        RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly run $flags --bin compact \
            -- --verify \
            D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

        for choice in --byte --wide --both ; do

            RUSTFLAGS="-C instrument-coverage" \
                cargo +nightly run $flags --bin compact \
                -- $choice \
                D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

            RUSTFLAGS="-C instrument-coverage" \
                cargo +nightly run $flags --bin compact \
                -- $choice --verify \
                D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

            for fmt in ascii utf8 utf8-color latex html html-color ; do

                RUSTFLAGS="-C instrument-coverage" \
                    cargo +nightly run $flags --bin compact \
                    -- $choice --format $fmt \
                    D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

                RUSTFLAGS="-C instrument-coverage" \
                    cargo +nightly run $flags --bin compact \
                    -- $choice --format $fmt --verify \
                    D__ D3_ D_2 D_3 D2_ D1_ D32 D211 DDD1D221D2D2D11

            done
        done
    fi

    # Rename profraw files to track which feature set they came from
    for file in default*.profraw; do
        if [ -f "$file" ]; then
            mv "$file" "${name}_${file}"
        fi
    done
done

# Merge all profiling data from all feature combinations
echo ""
echo "Merging coverage data from all feature combinations..."
$LLVM_PROFDATA merge -sparse *_default*.profraw -o combined.profdata

# Generate HTML report
echo "Generating HTML coverage report..."
$LLVM_COV show \
    --use-color \
    --format=html \
    --output-dir=htmlcov \
    --show-branches=count \
    --ignore-filename-regex='/.cargo/registry' \
    --ignore-filename-regex='/library/std/src/sys/thread_local/native/mod.rs' \
    --instr-profile=combined.profdata \
    $(find target/debug/deps -type f -perm +111 -name '*-[0-9a-f]*' | \
      grep -v '\.d$' | \
      sed 's/^/--object /')

# Generate text summary
echo "Generating text summary..."
$LLVM_COV report \
    --instr-profile=combined.profdata \
    $(find target/debug/deps -type f -perm +111 -name '*-[0-9a-f]*' | \
      grep -v '\.d$' | \
      sed 's/^/--object /') | \
    tee coverage_summary.txt

# Cleanup
rm -f *.profraw *.profdata

echo ""
echo "========================================="
echo "Coverage report generated in htmlcov/index.html"
echo "Summary saved to coverage_summary.txt"
echo "========================================="
