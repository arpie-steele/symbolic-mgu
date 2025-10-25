#!/usr/bin/env python3
"""
Find all potential valid proofs of length ≤ 5 that are NOT in subproofs.json.

A valid proof in condensed detachment:
- Starts at stack depth 0
- Ends at stack depth 1
- Never goes negative
- Uses: 1,2,3 (axioms, +1 to stack), D (modus ponens, -1 to stack, requires depth ≥2)
"""

import json
from pathlib import Path
from itertools import product

def is_valid_proof(proof_str):
    """Check if a proof string is valid according to stack rules."""
    depth = 0

    # Process in reverse (right to left)
    for char in reversed(proof_str):
        if char in '123':
            depth += 1
        elif char == 'D':
            if depth < 2:
                return False  # Can't use D without 2 items
            depth -= 1  # Pop 2, push 1 = net -1
        else:
            return False  # Invalid character

    return depth == 1  # Must end with exactly 1 item

def generate_all_valid_proofs(max_length):
    """Generate all valid proofs up to max_length."""
    valid_proofs = set()

    for length in range(1, max_length + 1):
        # Generate all possible strings of this length
        for combo in product('123D', repeat=length):
            proof_str = ''.join(combo)
            if is_valid_proof(proof_str):
                valid_proofs.add(proof_str)

    return sorted(valid_proofs, key=lambda x: (len(x), x))

def main():
    print("Generating all valid proofs of length ≤ 5...")
    all_valid = generate_all_valid_proofs(5)

    print(f"Found {len(all_valid)} theoretically valid proofs")
    print()

    # Group by length
    by_length = {}
    for proof in all_valid:
        length = len(proof)
        if length not in by_length:
            by_length[length] = []
        by_length[length].append(proof)

    for length in sorted(by_length.keys()):
        print(f"  Length {length}: {len(by_length[length])} proofs")

    print()

    # Load subproofs.json
    subproofs_file = Path(__file__).parent / 'subproofs.json'
    with open(subproofs_file, 'r') as f:
        subproofs_data = json.load(f)

    # Extract all subproof strings
    existing_subproofs = {entry['subproof'] for entry in subproofs_data}

    # Find missing proofs
    missing = [p for p in all_valid if p not in existing_subproofs]

    print(f"Checking against {len(existing_subproofs)} subproofs in subproofs.json...")
    print(f"Missing: {len(missing)} proofs not in our collection")
    print()

    if missing:
        print("Missing proofs by length:")
        missing_by_length = {}
        for proof in missing:
            length = len(proof)
            if length not in missing_by_length:
                missing_by_length[length] = []
            missing_by_length[length].append(proof)

        for length in sorted(missing_by_length.keys()):
            proofs = missing_by_length[length]
            print(f"\n  Length {length}: {len(proofs)} missing")
            for p in proofs:
                print(f"    {p}")
    else:
        print("✓ All theoretically valid proofs of length ≤5 exist in subproofs.json!")

    # Calculate impact on search space
    print("\n" + "="*70)
    print("SEARCH SPACE ANALYSIS")
    print("="*70)

    total_theoretical = 0
    total_actual = 0

    print("\nCandidates by length (theoretical vs actual):")
    for length in range(1, 6):
        # Theoretical: all strings with depth ending at 1
        # Rough estimate: branching factor ~3.5
        theoretical = int(3.5 ** length)

        # Actual valid proofs of this length
        actual = len(by_length.get(length, []))

        total_theoretical += theoretical
        total_actual += actual

        reduction = (1 - actual/theoretical) * 100 if theoretical > 0 else 0

        print(f"  Length {length}: ~{theoretical:6d} theoretical → {actual:3d} valid ({reduction:.1f}% pruned)")

    print()
    print(f"Total candidates length ≤5:")
    print(f"  Theoretical: ~{total_theoretical}")
    print(f"  Valid proofs: {total_actual}")
    print(f"  Reduction: {(1 - total_actual/total_theoretical)*100:.1f}%")

    print()
    print("If we assume missing proofs are impossible/useless:")
    print(f"  Further reduction: {len(missing)} / {total_actual} = {len(missing)/total_actual*100:.1f}%")

    # Extrapolate to longer proofs
    print()
    print("Effective branching factor analysis:")

    # Calculate actual branching from length 3 to 5
    if len(by_length.get(3, [])) > 0 and len(by_length.get(5, [])) > 0:
        # b^2 = count(5) / count(3) → b = sqrt(count(5) / count(3))
        b_actual = (len(by_length[5]) / len(by_length[3])) ** 0.5
        print(f"  Theoretical: b ≈ 3.5")
        print(f"  Actual (from data): b ≈ {b_actual:.2f}")
        print(f"  Improvement: {(1 - b_actual/3.5)*100:.1f}% reduction in branching")

        print()
        print("Impact on deeper search:")
        print(f"  Length 20: 3.5^20 = 7.7e10 vs {b_actual:.2f}^20 = {b_actual**20:.2e}")
        print(f"  Length 30: 3.5^30 = 4.4e15 vs {b_actual:.2f}^30 = {b_actual**30:.2e}")
        print(f"  Time savings: ~{(3.5/b_actual)**30:.1e}x faster")

if __name__ == '__main__':
    main()
