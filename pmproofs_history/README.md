# Principia Mathematica Proofs: A History of Optimization

This directory contains a historical archive of proof optimizations for the 193 theorems of propositional calculus from Whitehead and Russell's _Principia Mathematica_.

## Overview

These files represent a remarkable 25+ year effort (late 1990s - 2025) to find the shortest possible proofs for propositional calculus theorems using condensed detachment. The proofs are based on three axioms (ax-1, ax-2, ax-3) and modus ponens (ax-mp), using Meredith's condensed detachment notation from the 1950s.

## File Timeline

### Archived Historical Snapshots
| File | Date | Description |
|------|------|-------------|
| `pmproofs-orig.txt` | ~1990s | Original proofs by Norman Megill (193 theorems) |
| `pmproofs-2010-11-01.txt` | Nov 1, 2010 | Includes Gregory Bush's 67 improvements (2004) + Scott Fenton's Meredith axiom proof |
| `pmproofs-2012-01-23.txt` | Jan 23, 2012 | Scott Fenton's continued improvements |
| `pmproofs-2018-08-21.txt` | Aug 21, 2018 | George Szpiro's improvements, Peirce's axiom added |
| `pmproofs-2020-07-23.txt` | Jul 23, 2020 | Rohan Ridenour's improvements |

### Git Repository History (2022-Present)
| File | Date | Description |
|------|------|-------------|
| `pmproofs-git-2022-08-29.txt` | Aug 29, 2022 | Initial git commit, includes biass theorem, corrected Meredith proof |
| `pmproofs-git-2022-10-25.txt` | Oct 25, 2022 | Samiro Discher's first wave: 17 shorter proofs |
| `pmproofs-git-2023-04-17.txt` | Apr 17, 2023 | 5 shorter proofs (*3.44, *4.77, *4.85, *4.86, biass) |
| `pmproofs-git-2024-06-16.txt` | Jun 16, 2024 | 40 shorter proofs using pmGenerator --transform -z |
| `pmproofs.txt` | Mar 20, 2025 | Latest: 38 more shorter proofs using pmGenerator --transform -x (v1.2.2) |

## Key Achievements

### Overall Progress
- **92 theorems** have shorter proofs in the latest version (Mar 2025) compared to the original (1990s)
- **5,000+ total steps eliminated** across all improved proofs
- Some proofs are exhaustively verified to be optimal (all proofs ≤21 steps in original, ≤39 steps as of 2024)
- The git history (2022-2025) alone shows **95+ improvements** from automated tools

### Most Dramatic Improvements

| Theorem | Original Steps | Latest Steps | Reduction | Notes |
|---------|---------------|--------------|-----------|-------|
| Meredith's Axiom | 1459 | 141 | **-1318** | Single axiom for propositional calculus |
| *4.39 | 913 | 463 | **-450** | Associative law variant |
| *4.79 | 547 | 259 | **-288** | Complex implication chain |
| *5.36 | 417 | 257 | **-160** | Equivalence theorem |
| *4.78 | 327 | 191 | **-136** | Distributive property |
| *3.44 | 271 | 161 | **-110** | Negation simplification |

### Contributors Over Time

1. **Norman Megill (1990s)**: Original 193 proofs, exhaustive search for proofs ≤21 steps
2. **Gregory Bush (2004)**: Found shorter proofs for 67 theorems
3. **Scott Fenton (2010-2013)**: Meredith's single axiom proof, improvements to 15+ theorems
4. **George Szpiro (2018)**: Improvements including Peirce's axiom, shorter proof of *3.37
5. **Rohan Ridenour (2020)**: Multiple improvements including *2.6, *5.25, *5.31
6. **Samiro Discher (2022-2025)**: Massive improvements using automated tools (pmGenerator), 78+ theorems improved

## The Condensed Detachment Notation

Proofs use Meredith's condensed detachment notation (Polish notation, 1950s):
- `1` = ax-1: `(φ → (ψ → φ))`
- `2` = ax-2: `((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))`
- `3` = ax-3: `((¬φ → ¬ψ) → (ψ → φ))`
- `D` = ax-mp (modus ponens/detachment)

**Example**: The proof `DD2D121` for theorem *1.6 (7 steps) is entered in reverse order:
```
ax-1 ax-2 ax-1 ax-mp ax-2 ax-mp ax-mp
```

## Git History Analysis

The GitHub repository was created on **August 29, 2022**, by David A. Wheeler. The historical snapshots (2010, 2012, 2018, 2020) were included as archived references, while the actual `pmproofs.txt` file has its own commit history from 2022 onward.

### Key Findings from Git History:

1. **2022-08-29**: Initial commit includes **170 theorems** (vs 165 in the 2020-07-23 archive)
   - Added: `biass` theorem (completes axioms for classical equivalence logic)
   - Corrected: Meredith's axiom proof updated from 155 to 145 steps

2. **2022-10-25**: First automated improvements (Samiro Discher)
   - 17 shorter proofs discovered
   - Beginning of the pmGenerator era

3. **2023-04-17**: Targeted improvements
   - 5 theorems improved including *3.44, *4.77, *4.85, *4.86, biass

4. **2024-06-16**: Major breakthrough
   - **40 theorems** improved using `pmGenerator --transform -z`
   - Exhaustive search extended to 39 steps

5. **2025-03-20**: Latest improvements
   - **38 more theorems** improved using `pmGenerator --transform -x` (v1.2.2)
   - Generative proof compression techniques

### Evolution Example: Theorem *2.32

This theorem shows improvement only in the most recent automated search (2024):

```
Original-2023:    91 steps - 2D1D3DD2DD2D13DD2D1311
2024-2025:        83 steps - D2D13DD2D13111  (-8 steps)
```

## Evolution Example: Meredith's Axiom

Meredith's single axiom for propositional calculus shows the most dramatic evolution in the entire collection, with the proof reduced by over 90% through successive improvements:

```
Pre-2010:       1459 steps (original, proof too long to display)
2010 (SF):       205 steps (Scott Fenton: -1254 steps, -86%)
2018 (GSZ):      199 steps (George Szpiro: -6 steps)
2020 (RR):       145 steps (Rohan Ridenour: -54 steps)
2022 (SD):       141 steps (Samiro Discher: -4 steps)
```

**Total reduction: 1459 → 141 steps (-1318 steps, -90.3%)**

The theorem statement itself:
```
(((((P -> Q) -> (~ R -> ~ S)) -> R) -> T) -> ((T -> P) -> (S -> P)))
```

This single axiom, together with modus ponens, is sufficient to derive all of propositional calculus.

## Proof Verification

All proofs can be verified using:
1. **Metamath Solitaire Applet**: http://us.metamath.org/mmsolitaire/mms.html
2. **drule.c**: A C program for batch verification (available at http://us.metamath.org/downloads/drule.c)

To verify with drule.c:
```bash
gcc drule.c -o drule
./drule < pmproofs.txt > verified.txt
```

## Recent Automation Breakthrough

Samiro Discher's pmGenerator tool (2022-2025) represents a significant advance in automated proof compression:
- Uses generative proof compression with transforms (`--transform -x`, `-z`)
- Exhaustively searched proofs up to 39 steps
- Found improvements for 78+ theorems in recent versions
- Demonstrates the power of modern computational proof search

## Theoretical Context

These proofs implement formal reasoning based on:
- **Robinson's Resolution**: Unification-based theorem proving (1965)
- **Condensed Detachment**: Meredith's Polish notation for proofs (1950s)
- **Most General Unifier (MGU)**: The foundation of automated theorem proving

The progression from manual discovery (1990s-2018) to semi-automated tools (2020s) mirrors the broader evolution of computer-assisted mathematics.

## Relevance to This Project

The `symbolic-mgu` library implements the same core unification operations that enable proof search in this domain:
- `unify(term1, term2)`: Finds most general unifiers
- `apply(statement1, n, statement2)`: Condensed detachment operation
- `contract(statement, n, m)`: Hypothesis unification

These files serve as:
1. **Historical documentation** of proof optimization efforts spanning 25+ years
2. **Test cases** for unification algorithms (2,997 validated sub-proofs in `subproofs.json`)
3. **Benchmarks** for proof search performance (can your algorithm find the 5-step proof of *2.08?)
4. **Training data** for machine learning approaches to theorem proving
5. **Proof fragment library** for accelerating automated proof search

## Analysis Tools

### analyze_proofs.py
Tracks proof evolution across all versions:
- Parses all versions of the pmproofs files (including multi-line proofs)
- Tracks proof length evolution across time
- Identifies all improvements
- Generates statistics on optimization progress

Run with:
```bash
python3 analyze_proofs.py
```

### extract_subproofs.py
Extracts all valid subproofs (both complete proofs and fragments):
- Identifies all valid condensed detachment subproofs
- Tracks which theorems each sub-proof completely proves (via `proves_theorems` field)
- Includes proofs that appear first as fragments (e.g., `1` first appears in *1.2 but proves *1.3, *2.02, *2.07)
- Tracks only the first occurrence from the earliest source file
- Outputs JSON ordered by proof length, then lexicographically

Generates `subproofs.json` (1.1MB) containing 2,997 distinct subproofs:
- **336 complete theorem proofs** (proof strings that prove ≥1 theorem)
- **2,661 pure proof fragments** (reusable building blocks)

Run with:
```bash
python3 extract_subproofs.py
```

**Key findings:**
- **Single axiom proofs**:
  - `1` proves *1.3, *2.02, *2.07 (Add, Simp, Identity axioms)
  - `2` proves *2.76, *2.77
  - `3` proves *2.17 (Contraposition)
- **Multi-theorem proofs**:
  - `DD211` (5 chars) proves *2.08, *2.11, *2.53, *2.54 (Identity variants)
  - Many proof strings are reused across multiple theorems
- **Longest proofs**:
  - 1,883 chars (biass theorem)
  - 1,459 chars (Meredith's single axiom)

**Value for automated proof search:**
These 2,997 subproofs represent **25+ years of field-tested optimization** (1990s-2025):
- Manual discoveries by expert mathematicians
- Exhaustive computer searches up to 39 steps
- Recent automated improvements via pmGenerator
- Perfect as validation targets and benchmarks for new proof search algorithms

### validate_proofs.py
Validates α-equivalence of proof variants:
- Runs `cargo run --bin compact` on all distinct proofs
- Parses output (handling ANSI color codes)
- Verifies structural equivalence of resulting formulas
- Reports validation results

Run with:
```bash
python3 validate_proofs.py
```

### validate_proofs_drule.py
Alternative validator using the drule binary (avoids compact bugs):
- Uses `/Users/rpenner/Downloads/drule` for proof validation
- Outputs formulas in Polish notation and human-readable infix
- Confirms the same 7 theorems with formula mismatches
- Independent validation of proof correctness

Run with:
```bash
python3 validate_proofs_drule.py
```

### find_missing_short_proofs.py
Analyzes the theoretical search space for short proofs:
- Generates all theoretically valid proofs ≤5 characters
- Compares against `subproofs.json` to find missing proofs
- Calculates effective branching factor (2.45 vs theoretical 3.5)
- Shows search space reduction (~45,000× faster at length 30)

Run with:
```bash
python3 find_missing_short_proofs.py
```

**Key findings:**
- 48/66 theoretically valid short proofs are missing (72.7% pruning)
- Missing proofs fall into categories:
  - **DD1AB patterns**: Redundant with proof A (e.g., DD111, DD112, DD121, etc.)
  - **Unification failures**: D31, D32, D33, D3Dxx, DD2[23]x, DD3xxx
  - **Specializations**: D2D21, DD212 (less useful than DD211)
  - **Less useful variants**: D2D22, D2D23, D1D12, D1D13

**Efficient proof generation strategy:**

When implementing automated proof search, avoid generating redundant `DD1AB` patterns through syntactic pruning:

```python
def should_prune(proof_prefix, next_char):
    # Left-to-right generation: don’t prepend D to D1...
    if next_char == 'D' and proof_prefix.startswith('D1'):
        return True

    # Right-to-left generation: don’t continue after DD1
    if proof_prefix.endswith('DD1'):
        return True

    return False
```

This prunes branches **before** attempting unification, using only the proof string itself (no separate state needed). The pattern `DD1AB` is always equivalent to proof `A`, so these combinations can be rejected purely on syntactic grounds.

## Future Work

Potential areas for continued improvement:

**Using this data:**
1. Implement proof search using `subproofs.json` as a fragment library (macro operators)
2. Benchmark new algorithms against the 336 known complete proofs
3. Train machine learning models on the 2,997 validated proof patterns
4. Investigate the 7 theorems with non-α-equivalent proof variants (*2.64, *4.15, *4.45, *4.78, *4.79, *5.6, *5.75)

**Extending the research:**
5. Exhaustive search beyond 39 steps using modern computing power
6. Verification that current shortest proofs are truly optimal
7. Integration with automated theorem provers (e.g., Coq, Lean, Isabelle)
8. Extension to predicate calculus and other logical systems

## License

All files in this directory are in the **PUBLIC DOMAIN** per:
- Creative Commons Public Domain Dedication (original release by Norman Megill and Gregory Bush, 2007)
- CC0 Public Domain Dedication (current version)

See individual files for complete license information.

## References

- Metamath Home Page: http://us.metamath.org
- Metamath Solitaire: http://us.metamath.org/mmsolitaire/mms.html
- _Principia Mathematica_: Whitehead and Russell (1910-1913)
  - Volume 1: https://archive.org/details/alfred-north-whitehead-bertrand-russel-principia-mathematica.-1
  - Volume 2: https://archive.org/details/PrincipiaMathematicaVol2
  - University of Michigan Historical Math Collection: http://name.umdl.umich.edu/aat3201.0001.001
- pmGenerator: Samiro Discher's proof compression tool (2022+)
- Original paper on Meredith's notation: "A Finitely Axiomatized Formalization of Predicate Calculus with Equality"

---

*Archive compiled: October 2025*
*Source: https://github.com/metamath/metamath-website-seed/tree/main/mmsolitaire*
