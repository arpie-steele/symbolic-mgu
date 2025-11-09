# Our System

Every [STATEMENT] is a triple of an assertion [SENTENCE], an enumerated, possibly
empty, list of distinct hypothesis [SENTENCEs], and a [DISTINCTNESS graph] where the nodes
are [`Metavariables`] used in the [STATEMENT] and any edge between two [`Metavariables`] means
no substitution of a tree into one [`Metavariable`] may equal or include part of what was substituted for the other.

The hypotheses of a [STATEMENT] are stored as an ordered list but semantically treated as a set for equality;
operations like CONTRACT and APPLY require indices into that list.

[STATEMENT] A is included in [STATEMENT] B when there is an admissible mapping of
the [`Metavariables`] of B that makes its [SENTENCEs] identical to
those of A (modulo a possible renumbering of any hypotheses) and makes the edges a
subset of the edges of A.

When A and B mutually include each other, the mapping is of [`Metavariables`] to
[`Metavariables`] and we say A and B are identical.

Given an ordering on [`Metavariables`] of each type and an ordering on [NODEs],
it follows there is a canonical relabeling of the [`Metavariables`] and reordering
of the hypotheses, which creates an identical [STATEMENT] with minimal
lexicographic ordering, which we call its canonical form.

Likewise, given two [STATEMENTs] A and B, there is a C that is identical to B
but with all [`Metavariables`] disjoint from those of A.

Example: "<span lang="la">Modus Ponens</span>", a named rule, is a [STATEMENT] with
* an assertion, "<span lang="und-Zmth">β</span>",
* hypothesis 1, "<span lang="und-Zmth">Implies(α, β)</span>",
* hypothesis 2, "<span lang="und-Zmth">α</span>", and a
* [DISTINCTNESS graph] with no edges.

(<span lang="und-Zmth">Implies</span>, <span lang="und-Zmth">α</span> and <span lang="und-Zmth">β</span>, obviously, are of [TYPE] [`Boolean`].)

Let's define `CONTRACT(A, n, m)`, which takes [STATEMENT] `A` and attempts to
unify the contents of hypotheses numbered `n` and `m`, and if that is possible,
return the form with minimal lexicographic ordering.

Let's define `APPLY(A, n, B)`, which attempts to unify the contents of hypothesis
numbered `n` of [STATEMENT] `A` with the assertion of [STATEMENT] `B`. If that is possible,
the result has the remapped assertion of `A` and hypotheses consisting of the
(distinct) union of those that remain from `A` and any from `B`.