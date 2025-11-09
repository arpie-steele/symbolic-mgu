# Formal expression of the main content

## DISTINCTNESS Graph

Given a finite set of metavariables <span lang="und-Zmth">V</span>, a [DISTINCTNESS graph] is
an undirected graph <span lang="und-Zmth">G = (V, E)</span> where
  <span lang="und-Zmth">E ⊆ {{x, y} | x ≠ y ∈ V}</span>

An edge <span lang="und-Zmth">{x, y} ∈ E</span> enforces: No substitution may assign trees
to <span lang="und-Zmth">x</span> and <span lang="und-Zmth">y</span> that
share any metavariable in common.

## STATEMENT

A [STATEMENT] is a triple <span lang="und-Zmth">(A; H; D)</span> where:
* <span lang="und-Zmth">A</span> is the assertion, a [SENTENCE].
* <span lang="und-Zmth">H = \[H₁, ..., Hₙ\]</span> is a list of hypotheses, each a [SENTENCE].
* <span lang="und-Zmth">D</span> is a [DISTINCTNESS graph] over the set of all metavariables used in A and
  in any Hᵢ.

We require that <span lang="und-Zmth">A</span>, each <span lang="und-Zmth">Hᵢ</span>, and <span lang="und-Zmth">D</span>
be well-formed as per the above definitions.

## Substitution and Unification

A substitution, <span lang="und-Zmth">σ</span> is a partial function mapping metavariables
to trees of matching [TYPE].

We write <span lang="und-Zmth">τσ</span> for the tree resulting from applying substitution σ recursively
to all metavariables in <span lang="und-Zmth">τ</span>.

Two trees, <span lang="und-Zmth">τ₁</span> and <span lang="und-Zmth">τ₂</span> are unifiable
iff there exists a substitution, <span lang="und-Zmth">σ</span>, such that <span lang="und-Zmth">τ₁σ = τ₂σ</span>.

A substitution must be acyclic: no metavariable may map to a tree containing itself (the *occurs check*).

Note: The occurs check prevents cyclic *substitutions*, but does not restrict the
construction of self-referential *expressions*. Terms like <span lang="und-Zmth">Equals(A, A)</span>
or <span lang="und-Zmth">Contains(A, A)</span> are syntactically valid.
The system enforces structural well-formedness and type constraints, but does not
validate semantic correctness—that responsibility belongs to the user's choice of axioms.
For example, proving <span lang="und-Zmth">Equals(Union(x, y), Union(y, x))</span> is not the
system's responsibility; the user must supply such proofs from their chosen axioms.
Distinctness checks operate syntactically (shared metavariables), not semantically
(semantic equivalence). This intentional fragility to syntactic variation keeps the
system applicable to diverse logical frameworks.

A most general unifier (MGU) is a unifier, <span lang="und-Zmth">σ</span>, such that any other
unifier factors through <span lang="und-Zmth">σ</span> (that is, any other unifier <span lang="und-Zmth">σ'</span>
can be expressed as <span lang="und-Zmth">σ</span> followed by another substitution).

## Inclusion and Identity of [STATEMENTs]

Let <span lang="und-Zmth">S₁ = (A₁; H₁; D₁)</span> and <span lang="und-Zmth">S₂ = (A₂; H₂; D₂)</span>.

We say <span lang="und-Zmth">S₁ includes S₂</span> (written <span lang="und-Zmth">S₁ ⊇ S₂</span>)
iff there exists *any* substitution <span lang="und-Zmth">σ</span> such that:
* <span lang="und-Zmth">A₁σ = A₂</span> (S₁'s assertion, after substitution, equals S₂'s assertion);
* For each <span lang="und-Zmth">hᵢ</span> in <span lang="und-Zmth">H₁</span>,
  <span lang="und-Zmth">hᵢσ</span> equals some <span lang="und-Zmth">hⱼ</span> in <span lang="und-Zmth">H₂</span>
  (S₁'s hypotheses, after substitution, form a subset of S₂'s); and
* <span lang="und-Zmth">D₂</span> is a super-graph of <span lang="und-Zmth">D₁σ</span>
  (S₂'s distinctness constraints include all of S₁'s constraints after transformation).
  Note: Each edge {v₁, v₂} in D₁ transforms to edges between each metavariable in v₁σ and each metavariable in v₂σ.
  When a metavariable is substituted with a 0-arity node, it contributes no metavariables to the transformed graph.
  When substituted with a tree containing multiple metavariables, one original edge may become many edges.

Note: Multiple substitutions may satisfy these conditions. Any one suffices to demonstrate inclusion.

Intuitively: <span lang="und-Zmth">S₁ ⊇ S₂</span> means S₁ is **more general** and S₂ is **more specific**.
The substitution <span lang="und-Zmth">σ</span> specializes S₁ into S₂.

Equivalently, we can write <span lang="und-Zmth">S₂ ⊆ S₁</span> (S₂ is included in S₁),
meaning the same relation from the opposite perspective.

We say <span lang="und-Zmth">S₁</span> and <span lang="und-Zmth">S₂</span> are identical
iff <span lang="und-Zmth">S₁ ⊇ S₂</span> and <span lang="und-Zmth">S₂ ⊇ S₁</span>
(mutual inclusion via variable renaming).

### Example of Inclusion

Consider:
* <span lang="und-Zmth">S₁ = (P → P; []; {})</span> — An axiom with no hypotheses or distinctness constraints
* <span lang="und-Zmth">S₂ = ((x=x → y=y) → (x=x → y=y); [x ∈ ℕ]; {x≠y})</span> — A statement with hypothesis and distinctness

We have <span lang="und-Zmth">S₁ ⊇ S₂</span> (the axiom **includes** the statement) because:
* Substitution <span lang="und-Zmth">σ = {P ↦ (x=x → y=y)}</span> transforms S₁ into S₂:
* <span lang="und-Zmth">A₁σ = (P → P)σ = ((x=x → y=y) → (x=x → y=y)) = A₂</span> ✓
* <span lang="und-Zmth">H₁σ = []σ = [] ⊆ [x ∈ ℕ] = H₂</span> ✓
* <span lang="und-Zmth">D₁σ = {}σ = {} ⊆ {x≠y} = D₂</span> ✓

The axiom is **more general** (fewer constraints), the statement is **more specific** (more constraints).

## Canonical Form

A canonical (normalized) form of a [STATEMENT] is one where:
* Metavariables are renamed to be minimal under a fixed total ordering on <span lang="und-Zmth">𝑀ₜ</span> (this ordering is externally defined in each implementation),
* Hypotheses are reordered to be lexicographically minimal under that
  metavariable ordering, and
* Two [STATEMENTs] are equal if their canonical forms are identical.

## Relabeling Disjointness

Given two [STATEMENTs], <span lang="und-Zmth">S₁</span> and <span lang="und-Zmth">S₂</span>,
a disjoint copy <span lang="und-Zmth">S₂'</span> of <span lang="und-Zmth">S₂</span> is obtained
by renaming all metavariables in <span lang="und-Zmth">S₂</span> so that they are disjoint from
those in <span lang="und-Zmth">S₁</span>.

## Operation: `CONTRACT`

Given <span lang="und-Zmth">S = (A; H; D)</span> and indices <span lang="und-Zmth">n ≠ m</span>,

  `CONTRACT(S, n, m)`:

* Attempts to unify <span lang="und-Zmth">Hₙ</span> and <span lang="und-Zmth">Hₘ</span>.
* If unification fails or violates a constraint in <span lang="und-Zmth">D</span>, returns an error state.
* Else, applies the resulting MGU <span lang="und-Zmth">σ</span> to all parts of <span lang="und-Zmth">S</span>.
* Returns the [STATEMENT] with:
  * Updated assertion <span lang="und-Zmth">Aσ</span>
  * Hypotheses <span lang="und-Zmth">Hσ</span> with the <span lang="und-Zmth">n</span>th and <span lang="und-Zmth">m</span>th removed and the unified hypothesis added once. Note: the substitution may cause other hypothesis pairs to become identical, which are also eliminated (as hypotheses are treated semantically as a set).
  * A transformed [DISTINCTNESS graph] <span lang="und-Zmth">Dσ</span>: for each edge {v₁, v₂} in D, if v₁σ and v₂σ contain metavariables, add edges between all pairs of distinct metavariables from v₁σ and v₂σ.

## Operation: `APPLY`

Given two [STATEMENTs], <span lang="und-Zmth">S₁ = (A₁; H₁; D₁)</span> and <span lang="und-Zmth">S₂ = (A₂; H₂; D₂)</span>, and index <span lang="und-Zmth">n</span>:

  `APPLY(S₁, n, S₂)`:

* Relabel <span lang="und-Zmth">S₂ → S₂'</span>, to be disjoint from <span lang="und-Zmth">S₁</span>.
* Attempt to unify H₁\[n\] with the assertion of S₂'.
* If unification fails or violates distinctness requirements, return an error.
* Else, apply the MGU σ to:
  * A₁, all H₁ (excluding H₁\[n\]), and all H₂'
* Merge these as the new hypothesis list (eliminating duplicates, as hypotheses are treated semantically as a set)
* Merge [DISTINCTNESS graphs] under σ: for each edge {v₁, v₂} in D₁ or D₂, if v₁σ and v₂σ contain metavariables, add edges between all pairs of distinct metavariables from v₁σ and v₂σ
* Return a new [STATEMENT] in canonical form.

## Simple Axioms and Empty Structures

A [STATEMENT] with no hypotheses and no distinctness constraints (D has no edges) is called a **simple axiom**.
For example, the Simp axiom <span lang="und-Zmth">Implies(α, Implies(β, α))</span> is a simple axiom.

Constants are NODEs of arity 0.
There is no empty [SENTENCE].

## Practical Considerations

### Hypothesis Ordering: Operational vs. Semantic

Hypotheses are stored as an **ordered list** but treated **semantically as a set**:

* **Operationally**: The operations `APPLY(S₁, n, S₂)` and `CONTRACT(S, n, m)` require
  integer indices to identify which hypotheses to unify. The order matters for specifying
  which operation to perform.

* **Semantically**: Two statements that differ only in hypothesis ordering are considered
  identical (they mutually include each other). The ordering carries no logical meaning.

This creates a tension: indices are necessary to *perform* operations, but meaningless to
*interpret* results.

### Indices are Ephemeral

Hypothesis indices should **not** be considered stable across operations:

* `APPLY(S₁, n, S₂)` consumes hypothesis `n` from S₁, shifts remaining indices, and may
  add hypotheses from S₂
* Canonicalization reorders hypotheses to achieve minimal lexicographic ordering
* After any operation, the mapping from "old index" to "new index" is not preserved

Applications should not rely on indices persisting; they are purely operational handles
for the current statement.

### Why Canonical Form Matters

Because hypothesis permutations are semantically equivalent but operationally distinct,
a database of statements could accumulate many copies of the "same" statement with
different hypothesis orderings. Canonical form prevents this:

* Converts all equivalent statements to a single normal form
* Enables efficient deduplication and equality checking
* Provides a stable representation for storage and comparison

Without canonicalization, a proof search application might redundantly explore permutations
of previously-discovered statements.

### Application Design Pattern

The intended use case is an application that maintains a **database of canonical statements**
with **proof receipts**:

1. Start with a set of axioms (already in canonical form)
2. Apply `APPLY` and `CONTRACT` operations to generate new statements
3. Canonicalize each result before adding to the database
4. Store a receipt showing how each statement was derived (which axioms, which operations)
5. Check new statements for inclusion in existing statements before adding (avoid redundancy)

This pattern supports automated theorem discovery while managing the computational cost of
maintaining canonical forms.

### Computational Cost

Canonicalization is an **idealized process** with no guaranteed efficient algorithm:

* Finding minimal lexicographic ordering may require trying all hypothesis permutations
* With many hypotheses (especially those unconnected to the assertion), this becomes costly
* The current implementation attempts full canonicalization; applications with performance
  constraints may need to evaluate trade-offs

For practical proof search, limiting the number of hypotheses or using heuristics to prune
the search space may be necessary.
