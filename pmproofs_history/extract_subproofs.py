#!/usr/bin/env python3
"""
Extract all condensed detachment subproofs from PM proofs collection.

This script:
1. Parses all pmproofs files to collect proof strings
2. Identifies all valid subproofs (fragments that form complete proofs)
3. Tracks where each subproof appears (theorem, position, length)
4. Outputs JSON ordered by proof length, then lexicographically
5. Excludes fragments that are equivalent to complete proofs

A valid subproof is a substring that, when executed in isolation,
produces exactly one statement on the stack (stack depth: 0 -> 1).
"""

import json
import re
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple, Set

def parse_proof_file(filepath):
    """Extract theorem names and their proof strings from a pmproofs file."""
    proofs = {}

    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
        lines = f.readlines()

    # Skip header comments (look for the separator line)
    start_idx = 0
    for i, line in enumerate(lines):
        if '---' in line and i > 10:  # Find last separator line
            start_idx = i + 1

    current_theorem = None
    proof_lines = []

    for i in range(start_idx, len(lines)):
        line = lines[i].strip()

        # Skip empty lines and "Result of proof" lines
        if not line or 'Result of proof' in line or 'result of proof' in line:
            continue

        # Match theorem line
        theorem_match = re.search(r';\s*!\s*(\*?[\w.]+)', line)
        if theorem_match and not re.match(r'^[1-9D]+', line):
            theorem_name = theorem_match.group(1)
            if theorem_name and not theorem_name.endswith('steps') and not theorem_name == 'Result':
                current_theorem = theorem_name
                proof_lines = []
            continue

        # If we have a current theorem, collect proof lines
        if current_theorem:
            if ';' in line and 'step' in line:
                step_match = re.search(r';\s*!\s*(\d+)\s+step', line)
                if step_match:
                    proof_part = line.split(';')[0].strip()
                    if proof_part:
                        proof_lines.append(proof_part)

                    proof_text = ''.join(proof_lines)
                    step_count = int(step_match.group(1))

                    if proof_text and re.match(r'^[1-9D]+$', proof_text):
                        proofs[current_theorem] = {
                            'proof': proof_text,
                            'steps': step_count
                        }

                    current_theorem = None
                    proof_lines = []
            else:
                if re.match(r'^[1-9D]+', line):
                    proof_lines.append(line)

    return proofs

def is_valid_subproof(substring):
    """
    Check if a substring is a valid condensed detachment proof.

    A valid proof:
    - Starts with stack depth 0
    - Ends with stack depth 1
    - Never goes negative

    Proof notation (read right-to-left in reverse):
    - '1', '2', '3': push axiom (stack +1)
    - 'D': modus ponens (stack -1, pops 2 and pushes 1)
    """
    stack_depth = 0

    # Process in reverse (right to left)
    for char in reversed(substring):
        if char in '123':
            stack_depth += 1
        elif char == 'D':
            if stack_depth < 2:
                return False  # Not enough items for modus ponens
            stack_depth -= 1  # Pop 2, push 1 = net -1
        else:
            return False  # Invalid character

    return stack_depth == 1

def find_all_subproofs(proof_string):
    """
    Find all valid subproofs within a proof string.

    Returns list of (start_position, length, subproof_string) tuples.
    """
    subproofs = []
    n = len(proof_string)

    # Try all possible substrings
    for start in range(n):
        for end in range(start + 1, n + 1):
            substring = proof_string[start:end]

            # Only check strings with reasonable length (at least one axiom)
            if len(substring) >= 1 and is_valid_subproof(substring):
                subproofs.append((start, len(substring), substring))

    return subproofs

def collect_all_proofs():
    """Collect all proofs from all versions with source dates."""
    # Files in chronological order with dates
    files = [
        ('Original', 'pmproofs-orig.txt', '1990s'),
        ('2010-11-01', 'pmproofs-2010-11-01.txt', '2010-11-01'),
        ('2012-01-23', 'pmproofs-2012-01-23.txt', '2012-01-23'),
        ('2018-08-21', 'pmproofs-2018-08-21.txt', '2018-08-21'),
        ('2020-07-23', 'pmproofs-2020-07-23.txt', '2020-07-23'),
        ('2022-08-29', 'pmproofs-git-2022-08-29.txt', '2022-08-29'),
        ('2022-10-25', 'pmproofs-git-2022-10-25.txt', '2022-10-25'),
        ('2023-04-17', 'pmproofs-git-2023-04-17.txt', '2023-04-17'),
        ('2024-06-16', 'pmproofs-git-2024-06-16.txt', '2024-06-16'),
        ('2025-03-20', 'pmproofs.txt', '2025-03-20'),
    ]

    # Track all proofs: {proof_string: [(theorem, version, date, is_full_proof)]}
    all_proofs = defaultdict(list)

    # Track full proofs (complete theorem proofs)
    full_proof_strings = set()

    for version, filename, date in files:
        filepath = Path(__file__).parent / filename
        if not filepath.exists():
            continue

        proofs = parse_proof_file(filepath)
        for theorem, data in proofs.items():
            proof_str = data['proof']
            all_proofs[proof_str].append((theorem, version, date, True))
            full_proof_strings.add(proof_str)

    return all_proofs, full_proof_strings

def main():
    print("Collecting all proofs from all versions...")
    all_proofs, full_proof_strings = collect_all_proofs()

    print(f"Found {len(all_proofs)} distinct proof strings")
    print(f"Found {len(full_proof_strings)} full theorem proofs")

    # Track which theorems each proof string completely proves
    # {proof_string: set of theorem names}
    complete_proof_for = defaultdict(set)
    for proof_string, occurrences in all_proofs.items():
        for theorem, version, date, is_full in occurrences:
            if is_full:
                complete_proof_for[proof_string].add(theorem)

    # Track all subproofs: {subproof_string: first_occurrence_data}
    all_subproofs = {}

    print("\nExtracting subproofs from all proofs...")
    processed = 0
    for proof_string, occurrences in all_proofs.items():
        processed += 1
        if processed % 50 == 0:
            print(f"  Processed {processed}/{len(all_proofs)} proofs...")

        # Find earliest occurrence for this proof string
        earliest = min(occurrences, key=lambda x: x[2])  # x[2] is date

        # Find all subproofs in this proof string
        subproofs = find_all_subproofs(proof_string)

        # Record where each subproof appears (only if first time or earlier)
        for start_pos, length, subproof_str in subproofs:
            # Check if this subproof is a complete proof for any theorems
            proves_theorems = complete_proof_for.get(subproof_str, set())

            # If we haven't seen this subproof yet
            if subproof_str not in all_subproofs:
                all_subproofs[subproof_str] = {
                    'theorem': earliest[0],
                    'position': start_pos,
                    'length': length,
                    'source_date': earliest[2],
                    'version': earliest[1],
                    'proves_theorems': sorted(proves_theorems)
                }
            else:
                # Update if this occurrence is earlier
                if earliest[2] < all_subproofs[subproof_str]['source_date']:
                    all_subproofs[subproof_str] = {
                        'theorem': earliest[0],
                        'position': start_pos,
                        'length': length,
                        'source_date': earliest[2],
                        'version': earliest[1],
                        'proves_theorems': sorted(proves_theorems)
                    }

    print(f"Found {len(all_subproofs)} distinct subproofs (including complete theorem proofs)")

    # Build output structure
    output = []

    for subproof_str, first_occ in all_subproofs.items():
        entry = {
            'subproof': subproof_str,
            'length': len(subproof_str),
            'first_occurrence': first_occ
        }
        output.append(entry)

    # Sort by length, then lexicographically
    output.sort(key=lambda x: (x['length'], x['subproof']))

    # Write to JSON
    output_file = Path(__file__).parent / 'subproofs.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nWrote {len(output)} subproofs to {output_file}")

    # Print some statistics
    complete_proofs = [e for e in output if e['first_occurrence']['proves_theorems']]
    fragments = [e for e in output if not e['first_occurrence']['proves_theorems']]

    print("\nStatistics:")
    print(f"  Total subproofs: {len(output)}")
    print(f"  Complete theorem proofs: {len(complete_proofs)}")
    print(f"  Proof fragments: {len(fragments)}")
    print(f"  Shortest subproof: {output[0]['length']} chars")
    print(f"  Longest subproof: {output[-1]['length']} chars")

    # Show some examples
    print("\n  Sample complete theorem proofs:")
    for i, entry in enumerate(complete_proofs[:10], 1):
        occ = entry['first_occurrence']
        theorems = ', '.join(occ['proves_theorems'][:3])
        if len(occ['proves_theorems']) > 3:
            theorems += f" (+{len(occ['proves_theorems'])-3} more)"
        print(f"    {i}. '{entry['subproof']}' ({entry['length']} chars) - "
              f"Proves: {theorems}")

    print("\n  Sample shortest fragments:")
    for i, entry in enumerate(fragments[:5], 1):
        occ = entry['first_occurrence']
        print(f"    {i}. '{entry['subproof']}' ({entry['length']} chars) - "
              f"First in {occ['theorem']} at position {occ['position']}")

    # Longest subproofs
    print("\n  Top 10 longest subproofs:")
    for i, entry in enumerate(output[-10:], 1):
        occ = entry['first_occurrence']
        if occ['proves_theorems']:
            proof_type = f"Proves {len(occ['proves_theorems'])} theorem(s)"
        else:
            proof_type = "Fragment"
        print(f"    {i}. {entry['length']} chars ({proof_type}) - "
              f"First in {occ['theorem']} from {occ['source_date']}")

if __name__ == '__main__':
    main()
