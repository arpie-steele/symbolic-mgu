#!/usr/bin/env python3
"""
Validate proof improvements by checking α-equivalence of resulting formulas.

This script:
1. Collects all distinct proofs for each theorem across all versions
2. Runs 'cargo run --bin compact -- --long <proof>' for each
3. Parses the output (handling ANSI color codes)
4. Verifies α-equivalence of S-expressions
"""

import re
import subprocess
from pathlib import Path
from collections import defaultdict
import sys

# ANSI color code regex
ANSI_ESCAPE = re.compile(r'\x1b\[[0-9;]*m')

def strip_ansi(text):
    """Remove ANSI color codes from text."""
    return ANSI_ESCAPE.sub('', text)

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

def run_compact(proof_string):
    """Run the compact binary on a proof string and parse the output."""
    try:
        result = subprocess.run(
            ['cargo', 'run', '--bin', 'compact', '--', '--long', proof_string],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=Path(__file__).parent.parent  # Run from project root
        )

        output = result.stdout + result.stderr

        # Parse the output
        parsed = {
            'success': '✓ Success!' in output,
            'assertion': None,
            'sexp': None,
            'is_tautology': '✓ YES' in output,
            'hypothesis_count': None,
        }

        # Extract assertion (strip ANSI codes)
        assertion_match = re.search(r'Assertion:\s*(.+)', output)
        if assertion_match:
            parsed['assertion'] = strip_ansi(assertion_match.group(1).strip())

        # Extract S-expression
        sexp_match = re.search(r'S-exp:\s*(.+)', output)
        if sexp_match:
            parsed['sexp'] = strip_ansi(sexp_match.group(1).strip())

        # Extract hypothesis count
        if 'no hypotheses' in output:
            parsed['hypothesis_count'] = 0
        else:
            hyp_match = re.search(r'(\d+)\s+hypothes(?:is|es)', output)
            if hyp_match:
                parsed['hypothesis_count'] = int(hyp_match.group(1))

        return parsed

    except subprocess.TimeoutExpired:
        return {'success': False, 'error': 'Timeout'}
    except Exception as e:
        return {'success': False, 'error': str(e)}

def parse_sexp(sexp_str):
    """
    Parse an S-expression into a tree structure.
    Returns a tuple of (operator, *children) or a variable name.
    """
    sexp_str = sexp_str.strip()

    if not sexp_str.startswith('('):
        # It's a variable
        return sexp_str

    # Remove outer parens
    sexp_str = sexp_str[1:-1].strip()

    # Find the operator (first token)
    parts = []
    current = []
    depth = 0

    for char in sexp_str:
        if char == '(':
            depth += 1
            current.append(char)
        elif char == ')':
            depth -= 1
            current.append(char)
        elif char == ' ' and depth == 0:
            if current:
                parts.append(''.join(current))
                current = []
        else:
            current.append(char)

    if current:
        parts.append(''.join(current))

    if not parts:
        return None

    operator = parts[0]
    children = [parse_sexp(p) for p in parts[1:]]

    return (operator, *children)

def alpha_equivalent(sexp1, sexp2, var_map=None):
    """
    Check if two S-expressions are α-equivalent.

    Two expressions are α-equivalent if they have the same structure
    and variables can be consistently renamed to match.
    """
    if var_map is None:
        var_map = {}

    tree1 = parse_sexp(sexp1)
    tree2 = parse_sexp(sexp2)

    return trees_alpha_equivalent(tree1, tree2, var_map)

def trees_alpha_equivalent(tree1, tree2, var_map):
    """Check if two parsed expression trees are α-equivalent."""

    # Both are variables
    if isinstance(tree1, str) and isinstance(tree2, str):
        # If tree1 is already mapped, check consistency
        if tree1 in var_map:
            return var_map[tree1] == tree2
        # If tree2 is already mapped to something else, fail
        if tree2 in var_map.values() and tree1 not in var_map:
            # Check if any other variable maps to tree2
            for k, v in var_map.items():
                if v == tree2 and k != tree1:
                    return False
        # Create new mapping
        var_map[tree1] = tree2
        return True

    # Both are compound expressions
    if isinstance(tree1, tuple) and isinstance(tree2, tuple):
        # Must have same operator and arity
        if len(tree1) != len(tree2):
            return False
        if tree1[0] != tree2[0]:  # operator must match
            return False

        # Recursively check children
        for child1, child2 in zip(tree1[1:], tree2[1:]):
            if not trees_alpha_equivalent(child1, child2, var_map):
                return False

        return True

    # One is variable, one is compound - not equivalent
    return False

def collect_all_proofs():
    """Collect all proofs from all versions."""
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

    # theorem -> {proof_string: [(version, steps)]}
    theorem_proofs = defaultdict(lambda: defaultdict(list))

    for version, filename in files:
        filepath = Path(__file__).parent / filename
        if not filepath.exists():
            continue

        proofs = parse_proof_file(filepath)
        for theorem, data in proofs.items():
            proof_str = data['proof']
            steps = data['steps']
            theorem_proofs[theorem][proof_str].append((version, steps))

    return theorem_proofs

def main():
    print("Collecting all proofs from all versions...")
    theorem_proofs = collect_all_proofs()

    print(f"Found {len(theorem_proofs)} unique theorems\n")

    # Find theorems with multiple distinct proofs
    theorems_with_variants = {
        theorem: proofs
        for theorem, proofs in theorem_proofs.items()
        if len(proofs) > 1
    }

    print(f"Found {len(theorems_with_variants)} theorems with multiple proof variants\n")
    print("=" * 80)

    validation_results = []

    for theorem in sorted(theorems_with_variants.keys()):
        proofs = theorems_with_variants[theorem]
        proof_list = list(proofs.items())

        print(f"\nTheorem: {theorem}")
        print(f"  {len(proof_list)} distinct proofs")

        # Run compact on each proof
        results = []
        for proof_str, versions in proof_list:
            steps = versions[0][1]  # Get step count from first version
            print(f"    Testing proof: {steps} steps ({len(proof_str)} chars)")
            result = run_compact(proof_str)
            results.append((proof_str, steps, versions, result))

            if not result['success']:
                print(f"      ❌ FAILED: {result.get('error', 'Unknown error')}")
            elif not result['is_tautology']:
                print(f"      ⚠️  Not a tautology!")
            elif result['hypothesis_count'] != 0:
                print(f"      ⚠️  Has {result['hypothesis_count']} hypotheses")
            else:
                print(f"      ✓ Success: tautology, no hypotheses")

        # Check α-equivalence between all pairs
        all_equivalent = True
        for i in range(len(results)):
            for j in range(i + 1, len(results)):
                proof1, steps1, vers1, res1 = results[i]
                proof2, steps2, vers2, res2 = results[j]

                if not res1['success'] or not res2['success']:
                    continue

                if res1['sexp'] and res2['sexp']:
                    equivalent = alpha_equivalent(res1['sexp'], res2['sexp'])

                    if equivalent:
                        print(f"      ✓ Proofs with {steps1} and {steps2} steps are α-equivalent")
                    else:
                        print(f"      ❌ Proofs with {steps1} and {steps2} steps are NOT α-equivalent!")
                        print(f"         S-exp 1: {res1['sexp']}")
                        print(f"         S-exp 2: {res2['sexp']}")
                        all_equivalent = False

        validation_results.append((theorem, len(proof_list), all_equivalent))

    # Summary
    print("\n" + "=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)

    total_theorems = len(validation_results)
    all_valid = sum(1 for _, _, valid in validation_results if valid)

    print(f"\nTotal theorems with multiple proofs: {total_theorems}")
    print(f"All proofs α-equivalent: {all_valid}/{total_theorems}")

    if all_valid < total_theorems:
        print("\n❌ FAILURES:")
        for theorem, count, valid in validation_results:
            if not valid:
                print(f"  - {theorem}: {count} proofs, NOT all equivalent")
    else:
        print("\n✓ All proof variants are α-equivalent!")

    return 0 if all_valid == total_theorems else 1

if __name__ == '__main__':
    sys.exit(main())
