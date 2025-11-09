## What This Library Is

`symbolic-mgu` is a Rust crate for experimenting with **unification in symbolic logic**.
It provides a way to represent logical formulae as structured objects, then apply
operations like *unification*, *contraction*, and *application* in order to explore
the space of consequences that follow from given axioms.  

Rather than telling the machine *what* to prove, you give it rules,
and the library shows you *what can be unified*.

The library is intentionally minimal, focusing on correctness over convenience.
It enforces structural constraints (type matching, arity checking, occurs check)
but makes no assumptions about semantics or presentation. For example, while
operators like "and" are commutative and associative, the library doesn't
provide variadic syntax—you must choose whether And(α, β, γ) maps to
And(And(α, β), γ) or And(α, And(β, γ)). This keeps the system simple,
trustworthy, and free of semantic assumptions that would limit its applicability
to different logical frameworks.

---

## Why It Exists
### From Stoicism to Frege to Meredith

The history of logic moved from persuasive arguments (Stoics, Aristotle)<br>
→ to late 19th century symbolic notation (Frege, 1879)<br>
→ to 20th century mechanical proof systems (Hilbert, Meredith).

Frege gave us a formal notation in which logic could be carried out
and checked without reliance on human judgment. This paved the way
for mechanical reasoning systems, where proofs emerge from rules
applied to symbols. Around 1900, following Frege’s formal notation
and Hilbert’s program, the meaning of “proof” changed from a
persuasive argument expressed in natural language to a rigorously
formal sequence of symbolic steps governed by explicit rules —
something that could itself be studied and eventually mechanized.

Meredith, with his principle of *condensed&nbsp;detachment*, showed
that even complex derivations could be reduced to a simple operation
of substitution and inference.

Here, we take the next step, following Meredith: generalizing to unifications that
don’t always return to the rule of detachment (<span lang="la">modus ponens</span>).
With a *most general unifier* (MGU), the machine can search the
space of consequences from a given set of axioms — not by
prejudging what matters, but by systematically exploring what follows.

This library and its examples demonstrate how symbolic logic and
automated proof search can be expressed in code, letting the
machine discover paths through the landscape of formal reasoning.

The goal is not to automate every proof. We do not provide a way to
*find a particular proof* among the possibilities you supply.
Instead, the library offers a precise, programmable framework for exploring
how formulae transform under unification — and, given unlimited
time and space, for uncovering **all** reachable proofs.

---

## What You Can Do With It

### Core Unification Operations

- Define **[STATEMENTs]**: assertions with hypotheses and distinctness constraints
- **Unify** terms using Robinson's algorithm with occurs checking
- Use **`APPLY`** to connect one [STATEMENT]'s hypothesis with another's assertion
- Use **`CONTRACT`** to unify two hypotheses inside a [STATEMENT]
- Put [STATEMENTs] into **canonical form** for easier comparison of conveyed meaning
- Check **inclusion** (S₁ ⊇ S₂) and **identity** (S₁ ≡ S₂) between [STATEMENTs]

### Automated Theorem Discovery

- **Enumerate all Boolean terms** up to a specified depth using the `search` module
- Test whether a formula is a **tautology** by exhaustive evaluation
- Find **counterexamples** by searching for assignments that falsify a claim
- Systematically explore the space of **derivable theorems** from given axioms
- Memory-efficient iteration handles millions of terms without exhausting memory

### Error Handling & Validation

- Inspect **error conditions** with fine-grained error types:
  - Failed unification with descriptive messages
  - Distinctness constraint violations
  - Type mismatches between slots and trees
  - Index and arity errors

### Example Applications

Build theorem provers, proof assistants, or logic explorers:
- Implement condensed detachment systems (Meredith-style)
- Search for shortest proofs of propositional tautologies
- Discover new theorems reachable from axiom systems
- Validate proof steps in formal verification workflows
- Generate and test logical equivalences

This keeps the math rigorous, but gives you the tools to build
higher-level reasoning systems in Rust.

---

## Who It’s For

- **Rust developers** curious about logic programming and unification.  
- **Logicians / proof theorists** who want a programmable lab for testing rules.  
- **Anyone exploring automated reasoning** who prefers clarity and simplicity
  over heavyweight theorem provers.

---
