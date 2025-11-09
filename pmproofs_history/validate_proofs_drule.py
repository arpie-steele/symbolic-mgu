#!/usr/bin/env python3
"""
Validate proof variants using the drule binary.

This script:
1. Identifies theorems with multiple proof variants across all versions
2. Uses drule to compute the Polish notation for each proof
3. Verifies all variants produce the same formula (α-equivalence)
4. Reports any discrepancies
5. Displays formulas in both Polish notation and infix notation
"""

import json
import subprocess
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple, Optional

# Path to drule binary
DRULE_PATH = "/Users/rpenner/Downloads/drule"

def run_drule(proof_string: str) -> Tuple[bool, str, str]:
    """
    Run drule on a proof string.

    Returns:
        (success, stdout, stderr)
    """
    try:
        result = subprocess.run(
            [DRULE_PATH, proof_string],
            capture_output=True,
            text=True,
            timeout=5
        )
        return (result.returncode == 0, result.stdout.strip(), result.stderr.strip())
    except subprocess.TimeoutExpired:
        return (False, "", "Timeout")
    except Exception as e:
        return (False, "", str(e))

def polish_to_infix(polish: str, precedence_map: Optional[Dict[str, int]] = None) -> str:
    """
    Convert Polish notation to infix notation.

    Polish notation:
    - >AB means A → B
    - ~A means ¬A
    - Letters are variables

    Example: ">PP" → "(P → P)"
             ">>>PQP>>PQP" → "(((P → Q) → P) → ((P → Q) → P))"
    """
    if not polish:
        return ""

    if precedence_map is None:
        # Precedence: higher number = binds tighter
        precedence_map = {
            '→': 1,
            '¬': 2
        }

    def parse_expr(chars: List[str], pos: int) -> Tuple[int, str, int]:
        """
        Parse expression starting at position pos.

        Returns:
            (new_pos, expr_string, expr_precedence)
        """
        if pos >= len(chars):
            return (pos, "?", 0)

        char = chars[pos]

        # Negation
        if char == '~':
            new_pos, operand, op_prec = parse_expr(chars, pos + 1)
            # Negation binds tightly, no parens needed
            return (new_pos, f"¬{operand}", precedence_map['¬'])

        # Implication
        elif char == '>':
            pos1, left, left_prec = parse_expr(chars, pos + 1)
            pos2, right, right_prec = parse_expr(chars, pos1)

            # Add parens if needed
            left_str = f"({left})" if left_prec > 0 and left_prec <= precedence_map['→'] else left
            right_str = f"({right})" if right_prec > 0 and right_prec < precedence_map['→'] else right

            return (pos2, f"{left_str} → {right_str}", precedence_map['→'])

        # Variable (single letter)
        else:
            return (pos + 1, char, 999)  # Variables have highest precedence

    chars = list(polish)
    _, result, _ = parse_expr(chars, 0)
    return result

def parse_proof_file(filepath):
    """Extract theorem names and their proof strings from a pmproofs file."""
    import re

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

def collect_all_proofs():
    """Collect all proofs from all versions."""
    files = [
        ('Original', 'pmproofs-orig.txt'),
        ('2010-11-01', 'pmproofs-2010-11-01.txt'),
        ('2012-01-23', 'pmproofs-2012-01-23.txt'),
        ('2018-08-21', 'pmproofs-2018-08-21.txt'),
        ('2020-07-23', 'pmproofs-2020-07-23.txt'),
        ('2022-08-29', 'pmproofs-git-2022-08-29.txt'),
        ('2022-10-25', 'pmproofs-git-2022-10-25.txt'),
        ('2023-04-17', 'pmproofs-git-2023-04-17.txt'),
        ('2024-06-16', 'pmproofs-git-2024-06-16.txt'),
        ('2025-03-20', 'pmproofs.txt'),
    ]

    # Track all proofs: {theorem: [(proof_string, version, steps)]}
    all_proofs = defaultdict(list)

    for version, filename in files:
        filepath = Path(__file__).parent / filename
        if not filepath.exists():
            print(f"Warning: {filename} not found, skipping")
            continue

        proofs = parse_proof_file(filepath)
        for theorem, data in proofs.items():
            all_proofs[theorem].append((data['proof'], version, data['steps']))

    return all_proofs

def main():
    print("Collecting all proofs from all versions...")
    all_proofs = collect_all_proofs()

    # Find theorems with multiple distinct proofs
    theorems_with_variants = {}
    for theorem, proofs in all_proofs.items():
        distinct_proofs = list(set(p[0] for p in proofs))
        if len(distinct_proofs) > 1:
            theorems_with_variants[theorem] = distinct_proofs

    print(f"Found {len(theorems_with_variants)} theorems with multiple proof variants")
    print()

    if not theorems_with_variants:
        print("All theorems have unique proofs.")
        return

    # Validate each theorem's variants using drule
    validation_results = {}

    for theorem in sorted(theorems_with_variants.keys()):
        variants = theorems_with_variants[theorem]
        print(f"Validating {theorem} ({len(variants)} variants)...")

        results = []
        for i, proof in enumerate(variants, 1):
            success, stdout, stderr = run_drule(proof)

            if success:
                polish = stdout
                infix = polish_to_infix(polish)
                results.append({
                    'proof': proof,
                    'polish': polish,
                    'infix': infix,
                    'valid': True
                })
                print(f"  Variant {i}: {proof} ({len(proof)} chars)")
                print(f"    Polish: {polish}")
                print(f"    Infix:  {infix}")
            else:
                results.append({
                    'proof': proof,
                    'error': stderr,
                    'valid': False
                })
                print(f"  Variant {i}: {proof} ({len(proof)} chars)")
                print(f"    ERROR: {stderr}")

        # Check if all valid variants produce the same formula
        valid_results = [r for r in results if r['valid']]

        if len(valid_results) == 0:
            validation_results[theorem] = {
                'status': 'ALL_INVALID',
                'variants': results
            }
            print(f"  ✗ ALL VARIANTS INVALID")
        elif len(valid_results) < len(results):
            validation_results[theorem] = {
                'status': 'SOME_INVALID',
                'variants': results
            }
            print(f"  ⚠ SOME VARIANTS INVALID ({len(valid_results)}/{len(results)} valid)")
        else:
            # Check if all Polish notations are identical
            polish_strings = [r['polish'] for r in valid_results]
            if len(set(polish_strings)) == 1:
                validation_results[theorem] = {
                    'status': 'PASS',
                    'variants': results
                }
                print(f"  ✓ All variants produce identical formula")
            else:
                validation_results[theorem] = {
                    'status': 'FORMULA_MISMATCH',
                    'variants': results
                }
                print(f"  ✗ FORMULA MISMATCH")
                print(f"    Different formulas produced:")
                for r in valid_results:
                    print(f"      {r['proof']}: {r['infix']}")

        print()

    # Summary
    print("=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print()

    status_counts = defaultdict(int)
    for theorem, result in validation_results.items():
        status_counts[result['status']] += 1

    print(f"Total theorems with variants: {len(validation_results)}")
    print(f"  PASS (all variants equivalent): {status_counts['PASS']}")
    print(f"  FORMULA_MISMATCH: {status_counts['FORMULA_MISMATCH']}")
    print(f"  SOME_INVALID: {status_counts['SOME_INVALID']}")
    print(f"  ALL_INVALID: {status_counts['ALL_INVALID']}")
    print()

    # Show problematic theorems
    if status_counts['FORMULA_MISMATCH'] > 0:
        print("Theorems with formula mismatches:")
        for theorem, result in validation_results.items():
            if result['status'] == 'FORMULA_MISMATCH':
                print(f"  {theorem}")
                for r in result['variants']:
                    if r['valid']:
                        print(f"    {r['proof']}: {r['infix']}")
        print()

    if status_counts['SOME_INVALID'] > 0:
        print("Theorems with some invalid variants:")
        for theorem, result in validation_results.items():
            if result['status'] == 'SOME_INVALID':
                print(f"  {theorem}")
                for r in result['variants']:
                    if not r['valid']:
                        print(f"    {r['proof']}: {r['error']}")
        print()

    # Save results to JSON
    output_file = Path(__file__).parent / 'validation_results_drule.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(validation_results, f, indent=2, ensure_ascii=False)

    print(f"Detailed results saved to {output_file}")

if __name__ == '__main__':
    main()
