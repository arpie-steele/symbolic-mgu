#!/usr/bin/env python3
"""
Analyze pmproofs files to track the evolution of proof lengths over time.
"""

import re
from pathlib import Path
from collections import defaultdict

def parse_proof_file(filepath):
    """Extract theorem names and their proof lengths from a pmproofs file."""
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
    in_proof = False

    for i in range(start_idx, len(lines)):
        line = lines[i].strip()

        # Skip empty lines and "Result of proof" lines
        if not line or 'Result of proof' in line or 'result of proof' in line:
            continue

        # Match theorem line like: ((P v P) -> P); ! *1.2 Taut
        # The theorem name is after the !
        theorem_match = re.search(r';\s*!\s*(\*?[\w.]+)', line)
        if theorem_match and not re.match(r'^[1-9D]+', line):
            # This is a theorem declaration, not a proof
            theorem_name = theorem_match.group(1)
            # Filter out things that aren't theorem names
            if theorem_name and not theorem_name.endswith('steps') and not theorem_name == 'Result':
                current_theorem = theorem_name
                proof_lines = []
                in_proof = False
            continue

        # If we have a current theorem, start collecting proof lines
        if current_theorem:
            # Check if this line ends the proof (contains step count)
            if ';' in line and 'step' in line:
                # This is the final proof line with step count
                step_match = re.search(r';\s*!\s*(\d+)\s+step', line)
                if step_match:
                    # Extract any proof text before the semicolon
                    proof_part = line.split(';')[0].strip()
                    if proof_part:
                        proof_lines.append(proof_part)

                    # Combine all proof lines
                    proof_text = ''.join(proof_lines)
                    step_count = int(step_match.group(1))

                    # Verify the proof text looks valid (only contains expected characters)
                    if proof_text and re.match(r'^[1-9D]+$', proof_text):
                        proofs[current_theorem] = {
                            'proof': proof_text,
                            'steps': step_count
                        }

                    current_theorem = None
                    proof_lines = []
                    in_proof = False
            else:
                # This is a continuation line, accumulate it
                # Only accumulate lines that look like proof text
                if re.match(r'^[1-9D]+', line):
                    proof_lines.append(line)
                    in_proof = True

    return proofs

def main():
    # Define files in chronological order
    files = [
        ('Original', 'pmproofs-orig.txt'),
        ('2010-11-01', 'pmproofs-2010-11-01.txt'),
        ('2012-01-23', 'pmproofs-2012-01-23.txt'),
        ('2018-08-21', 'pmproofs-2018-08-21.txt'),
        ('2020-07-23', 'pmproofs-2020-07-23.txt'),
        ('2022-08-29-git', 'pmproofs-git-2022-08-29.txt'),
        ('2022-10-25-git', 'pmproofs-git-2022-10-25.txt'),
        ('2023-04-17-git', 'pmproofs-git-2023-04-17.txt'),
        ('2024-06-16-git', 'pmproofs-git-2024-06-16.txt'),
        ('2025-03-20-git', 'pmproofs.txt'),
    ]

    # Parse all files
    all_proofs = {}
    for version, filename in files:
        filepath = Path(__file__).parent / filename
        if filepath.exists():
            all_proofs[version] = parse_proof_file(filepath)
            print(f"Parsed {version}: {len(all_proofs[version])} theorems")
        else:
            print(f"Warning: {filename} not found")

    # Collect all theorem names
    all_theorems = set()
    for proofs in all_proofs.values():
        all_theorems.update(proofs.keys())

    print(f"\nTotal unique theorems found: {len(all_theorems)}")

    # Track improvements
    improvements = []
    for theorem in sorted(all_theorems):
        history = []
        for version, _ in files:
            if version in all_proofs and theorem in all_proofs[version]:
                steps = all_proofs[version][theorem]['steps']
                history.append((version, steps))

        # Check if proof got shorter over time
        if len(history) > 1:
            original_steps = history[0][1]
            final_steps = history[-1][1]
            if final_steps < original_steps:
                improvements.append((theorem, original_steps, final_steps,
                                   original_steps - final_steps))

    # Report improvements
    print(f"\n{len(improvements)} theorems have shorter proofs in the latest version:")
    print("\nTheorem    Original -> Latest   Improvement")
    print("-" * 50)
    for theorem, orig, final, diff in sorted(improvements, key=lambda x: -x[3]):
        print(f"{theorem:12s} {orig:3d} -> {final:3d}      -{diff:2d} steps")

    total_reduction = sum(diff for _, _, _, diff in improvements)
    print(f"\nTotal steps reduced: {total_reduction}")

    # Show some example proofs that evolved
    print("\n" + "=" * 70)
    print("Example theorem evolution (showing first 5 with improvements):")
    print("=" * 70)
    for theorem, orig, final, diff in improvements[:5]:
        print(f"\n{theorem}:")
        for version, _ in files:
            if version in all_proofs and theorem in all_proofs[version]:
                proof_data = all_proofs[version][theorem]
                print(f"  {version:12s}: {proof_data['steps']:3d} steps - {proof_data['proof']}")

if __name__ == '__main__':
    main()
