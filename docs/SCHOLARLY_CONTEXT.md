# Scholarly Context and Mathematical Foundations

## Mathematical Background

The **symbolic-mgu** crate implements typed symbolic unification—the process of finding most general unifiers (MGUs) between symbolic expressions—and supports inference via *condensed detachment*. These mechanisms, first formalized by Robinson (1965) and Meredith (1968), remain central to the automation of logical reasoning. The project's goal is to expose the algebraic and computational essence of unification in a safe, modular Rust design.

## Reproducible Experiments

Each API component is designed for reproducibility and inspection. Developers can reproduce or compare unifiers deterministically, trace factory operations, and serialize internal representations. This approach aims to make symbolic reasoning experiments both *verifiable* and *auditable*, aligning with open-science standards in formal methods.

## Relation to Prior Work

The **symbolic-mgu** crate situates itself in a lineage beginning with **Robinson's** (1965) introduction of unification as the computational core of resolution, extended through **Meredith's** (1953) development of *condensed detachment* as a minimal, self-contained inference rule.
Where traditional implementations have been largely untyped and imperative, this project re-casts those foundations in a *strongly-typed, ownership-safe* setting.
Rust's type system enforces invariants—such as variable distinctness, substitution immutability, and occurs-check soundness—that earlier theorem provers expressed only informally.
The result is both a research platform for exploring symbolic reasoning and a reproducible, audit-friendly implementation that demonstrates how modern programming languages can make the classical machinery of unification precise, efficient, and verifiable.

Unlike large monolithic provers such as **Prover9** or minimalist goal-directed systems like **leanCoP**, **symbolic-mgu** focuses narrowly on the *algebra of unification itself* rather than full proof search.
Its aim is to make the unifier and substitution machinery transparent, typed, and modular—objects that can be inspected, serialized, or extended by other reasoning engines.
In this sense, the crate serves as a *research kernel*: it exposes the mechanisms underlying condensed detachment and term rewriting without committing to a particular logic or search strategy.
That separation of concerns—between symbolic correctness and procedural heuristics—makes the project a bridge between classical logic programming theory and modern typed functional design.

## Mathematical References and Books for Further Reading

### Historical & Philosophical Foundations

- **Marcus Aurelius** (167). *Meditations*
  Stoic philosophy emphasizing rational analysis—a precursor to treating mathematical reasoning as procedure rather than intuition.

- **Frege, G.** (1879). *Begriffsschrift, eine der arithmetischen nachgebildete Formelsprache des reinen Denkens*
  (Concept Script, a formal language of pure thought modelled upon that of arithmetic).

- **van Heijenoort, J.** (1967). *From Frege to Gödel, a source book in mathematical logic, 1879–1931*
  Contains a translation of Frege (1879).

### Classical Logic & Proof Theory

- **Smullyan, R.** (1968) *First-Order Logic*
  Also available as a 1995 Dover Publications reprint.

- **Schütte, K.** (1977). *Proof Theory*

- **Smith, P.** (2020). *An Introduction to Formal Logic*, 2nd ed.

### Condensed Detachment

- **Meredith, C. A.** (1953). *Single axioms for the systems (C,N), (C,O) and (A,N) of the two-valued propositional calculus.*
  *The Journal of Computing Systems, 3*, 155–164.
  Available at <https://archive.org/details/journal-of-computing-systems_1953-07_1_3/page/155/mode/2up>

- **Meredith, D.** (1977). *In Memoriam: Carew Arthur Meredith 1904–1976.*
  *Notre Dame Journal of Formal Logic, XVIII*(4), October 1977.
  Available at <https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-18/issue-4/In-memoriam-Carew-Arthur-Meredith-1904--1976/10.1305/ndjfl/1093888116.pdf>

- **Kalman, J. A.** (1983). *Condensed detachment as a rule of inference.*
  *Studia Logica, 42*(4), 443–451.
  Available at <https://www.jstor.org/stable/20015133>

### Unification Theory and Algorithms

- **Robinson, J. A.** (1965). *A Machine-Oriented Logic Based on the Resolution Principle.*
  *Journal of the ACM, 12*(1), 23–41.
  Available at <https://dl.acm.org/doi/abs/10.1145/321250.321253>

- **Plotkin, G. D.** (1972). *Building-in Equational Theories.*
  *Machine Intelligence 7*, Edinburgh University Press, 73–90.

- **Martelli, A., & Montanari, U.** (1982). *An Efficient Unification Algorithm.*
  *ACM Transactions on Programming Languages and Systems, 4*(2), 258–282.
  Available at <https://dl.acm.org/doi/abs/10.1145/357162.357169>

### Automated Theorem Proving: Textbooks

- **Chang & Lee** (1973). *Symbolic Logic and Mechanical Theorem Proving*

- **Wos, L., Overbeek, R., Lusk, E., & Boyle, J.** (1992). *Automated Reasoning: Introduction and Applications* (2nd ed.).
  McGraw-Hill, Inc., New York.

- **Fitting, M.** (1996). *First-Order Logic and Automated Theorem Proving*

### Automated Theorem Proving: Systems and Implementations

- **Wos, L., Robinson, G., & Carson, D.** (1965). *Efficiency and Completeness of the Set of Support Strategy in Theorem Proving.*
  *Journal of the ACM, 12*(4), 536–541.
  Available at <https://dl.acm.org/doi/abs/10.1145/321296.321302>

- **Beckert, B., & Posegga, J.** (1994). *LeanT<sup>A</sup>P: Lean tableau-based deduction.*
  In *CADE-12*, Lecture Notes in Computer Science 814, pp. 793–797. Springer-Verlag.
  DOI: <https://doi.org/10.1007/3-540-58156-1_62>

- **Beckert, B., & Posegga, J.** (1995). *LeanT<sup>A</sup>P: Lean tableau-based deduction.*
  *Journal of Automated Reasoning 15*, 339-358
  DOI: <https://doi.org/10.1007/BF00881804>
  Preprint available at: <https://formal.kastel.kit.edu/beckert/pub/LeanTAP.pdf>

- **Otten, J., & Bibel, W.** (2003). *leanCoP: Lean connection-based theorem proving.*
  *Journal of Symbolic Computation, 36*(1-2), 139–161.
  Available at: <https://www.sciencedirect.com/science/article/pii/S0747717103000373>

- **Otten, J.** (2016). *nanoCoP: A Non-clausal Connection Prover.*
  In *Automated Reasoning, IJCAR 2016*,  Lecture Notes in Computer Science, LNAI 9706, pp. 302–312. Springer.
  DOI: <https://doi.org/10.1007/978-3-319-40229-1_21>

- **McCune, W.** (2005–2010). *Prover9 and Mace4.*
  <http://www.cs.unm.edu/~mccune/prover9/>

- **Megill, N. and Wheeler, D. A.** (2019) *Metamath: A Computer Language for Mathematical Proofs*. Lulu Press.
  Available at: <https://us.metamath.org/downloads/metamath.pdf>
  There is an errata page at: <https://github.com/metamath/metamath-book/blob/master/errata.md>
  Also, many worked examples at: <https://us.metamath.org>

### Broader Perspectives

- **Hofstadter, D.** (1980). *Gödel, Escher, Bach: An Eternal Golden Braid*

- **Stillwell, J.** (2022). *The Story of Proof: Logic and the History of Mathematics*

## Citation and Scholarly Use

If you use **symbolic-mgu** in published research, please cite it as a software artifact alongside foundational works like Robinson (1965), for example:

> *symbolic-mgu (v0.1.x)* — a Rust library for typed symbolic unification and condensed detachment.
> Available at [crates.io/crates/symbolic-mgu](https://crates.io/crates/symbolic-mgu).

## Acknowledgments

Thank you to the Metamath community.

Editorial and explanatory materials in this project were prepared with the assistance of **OpenAI's ChatGPT (GPT-5)** and **Anthropic's Claude (Claude Sonnet 4.5)**, used under the direction and review of the project maintainer.
All design, implementation, and interpretive decisions remain those of the human contributors.
This acknowledgment is included for scholarly transparency in keeping with best practices for AI-assisted research and technical documentation.
