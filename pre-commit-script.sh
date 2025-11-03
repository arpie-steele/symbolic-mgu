#!/bin/sh

# rm -f Cargo.lock
cargo +1.77 spellcheck || exit 1
cargo +1.77 fmt || exit 1

# Generate SVG diagrams from PlantUML sources if available
if command -v plantuml >/dev/null 2>&1; then
    if [ -d "docs/diagrams" ]; then
        echo "Generating SVG diagrams from PlantUML sources..."
        plantuml --progress-bar -f svg docs/diagrams || exit 1
    else
        echo "Note: docs/diagrams directory not found, skipping diagram generation"
    fi
else
    echo "Note: plantuml not found, skipping diagram generation"
fi

cargo +1.77 check --all-features --all-targets || exit 1
cargo +1.77 clippy --all-features --all-targets || exit 1
cargo +1.77 build --all-features --all-targets || exit 1
# cargo +1.77 run --all-features || exit 1
cargo +1.77 test --all-features || exit 1
cargo +1.77 doc --all-features || exit 1
cargo +1.77 publish --dry-run --allow-dirty || exit 1

echo ''
git status --ignored=matching
echo ''
echo 'Looks good to commit.'
