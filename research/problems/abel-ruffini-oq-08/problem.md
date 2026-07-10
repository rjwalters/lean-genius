# Problem: Formalizing Arnold's Topological Proof of Abel-Ruffini

**Slug**: abel-ruffini-oq-08
**Created**: 2026-07-09T16:57:40-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $\Sigma_n = \{(a_0, \dots, a_{n-1}) \in \mathbb{C}^n : z^n + a_{n-1} z^{n-1} + \dots + a_0 \text{ has a repeated root}\}$ be the discriminant locus, and let $M_n = \mathbb{C}^n \setminus \Sigma_n$ be its complement. The map sending a point of $M_n$ to the unordered set of roots of the corresponding polynomial is a covering map whose monodromy realizes the symmetric group $S_n$ acting on the roots. Arnold's theorem states:

$$
\text{For } n \ge 5, \text{ there is no formula for the roots of } z^n + a_{n-1}z^{n-1} + \cdots + a_0 = 0 \text{ built from } a_0, \dots, a_{n-1} \text{ using } +, -, \times, \div \text{ and radicals } \sqrt[k]{\,\cdot\,}, \text{ because the monodromy group } \pi_1(M_n) \twoheadrightarrow S_n \text{ contains a non-solvable image whose iterated commutator subgroups never terminate at the identity.}
$$

The open question: can this **topological** argument — monodromy of the root-covering over $M_n = \mathbb{C}^n \setminus \Delta$, the non-triviality of all higher commutators forced by $A_5 \le S_n$ being perfect, and the obstruction to expressing roots by radicals — be formalized in Lean 4, as opposed to the purely Galois-theoretic route already in Mathlib?

### Plain Language

There is a classical fact (Abel-Ruffini) that the general quintic and higher-degree polynomials have no solution formula using only arithmetic and root extractions. The standard proof uses Galois theory: the splitting field of a "generic" degree-$n$ polynomial has Galois group $S_n$, which is not solvable for $n \ge 5$. Vladimir Arnold gave a completely different, topological proof: as the coefficients of a polynomial travel in loops around the "bad set" where roots collide (the discriminant locus), the roots get permuted, generating $S_n$. A radical formula would force these monodromy permutations to sit inside a solvable tower of subgroups; Arnold shows the iterated commutators of the monodromy never die, so no such formula can exist. This problem asks whether that geometric/topological argument can be captured in Lean 4.

### Why This Matters

Arnold's proof is one of the most celebrated "proofs from the topological book": it replaces algebraic solvability by the purely topological fact that certain commutators of loops are non-trivial, and it is the historical seed of topological Galois theory (Khovanskii). Formalizing it would (1) give Lean a second, conceptually independent certificate for Abel-Ruffini, complementing the Galois-theoretic `AbelRuffini` proof; (2) exercise Mathlib's algebraic topology (`FundamentalGroup`, covering spaces, `π₁`) against a substantive classical theorem rather than toy examples; and (3) surface exactly which pieces of the monodromy/covering-space toolkit Mathlib is still missing. It is a landmark on Wiedijk's "100 theorems" list and a natural extension of the existing Abel-Ruffini gallery cluster.

## Known Results

### What's Already Proven

- `abel-ruffini` — the Galois-theoretic Abel-Ruffini theorem is fully formalized in this gallery (`Proofs/AbelRuffini.lean`) and in Mathlib as `Polynomial.Gal.not_solvable` / `AbelRuffini`-style results, using `solvableByRad ↔ IsSolvable (Gal p)`.
- Solvability of a group and its behavior under the derived series is in `Mathlib.GroupTheory.Solvable`; the key input $\neg\,\mathrm{IsSolvable}\,(S_5)$ is `Equiv.Perm.not_solvable` (via $A_5$ being simple and non-abelian, `alternatingGroup` results in `Mathlib.GroupTheory.SpecificGroups.Alternating`).
- The fundamental group and covering-space machinery exist in `Mathlib.Topology.Homotopy.FundamentalGroup` and `Mathlib.Topology.Covering`; loop concatenation and `π₁` group structure are available.

### What's Still Open

- No Lean formalization connects the monodromy of the discriminant-complement covering to the Galois group; the isomorphism $\pi_1(M_n)/\!\sim \;\to S_n$ (monodromy representation) is not in Mathlib.
- The configuration space $\mathrm{Conf}_n(\mathbb{C})$ / discriminant complement $M_n = \mathbb{C}^n \setminus \Delta$ and the fact that the root map is a covering are not formalized.
- The "solvability of a radical formula forces solvable monodromy" obstruction — Arnold's core lemma that a $k$-th root introduces at most an abelian layer, so a radical tower yields a subnormal series with abelian quotients — has no Lean counterpart in topological terms.

### Our Goal

Not to formalize Arnold's whole proof at once (that is a multi-year program), but to lay honest scaffolding: state the discriminant complement $M_n$, the root-covering, and the monodromy homomorphism $\pi_1(M_n) \to S_n$ as definitions/axioms, and prove the group-theoretic obstruction cleanly — that if the roots were given by a radical formula, the monodromy image would be solvable, contradicting $\neg\,\mathrm{IsSolvable}\,(S_5)$. The topological inputs (covering, surjectivity of monodromy) may initially be stated as hypotheses/axioms and reduced over time.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini | Same theorem via Galois theory; the target of the topological reformulation | Galois groups, solvable groups, `solvableByRad` |
| abel-ruffini-oq-07-discriminant | Discriminant locus $\Delta$ appears identically as the branch set of the covering | Discriminant of polynomials, resultants |
| abel-ruffini-galois-extensions | Structure of the derived series / solvable towers that the monodromy must violate | Solvable series, commutator subgroups |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Group-theoretic core with topological axioms**: Introduce `M n` (discriminant complement) and axiomatize the monodromy surjection `monodromy : FundamentalGroup (M n) x →* Equiv.Perm (Fin n)` as surjective. Then prove: a radical formula for the roots yields a factorization of the monodromy through a solvable group, so its image is solvable; combined with surjectivity onto $S_n$ and `not_solvable (S 5)`, derive the contradiction.
   - Why it might work: the genuinely novel content is the "radical ⇒ solvable monodromy" lemma, which is essentially group theory once the covering vocabulary is fixed; Mathlib already has `IsSolvable`, derived series, and `not_solvable`.
   - Risk: the interface for "a radical formula" in topological/covering terms is delicate; getting it faithful (not circular with the Galois version) requires care.

2. **Approach B — Build the covering space genuinely**: Define $M_n = \mathbb{C}^n \setminus \Delta$ as an open subset, show the root map $\mathrm{Conf}_n(\mathbb{C}) \to M_n$ is a covering (`IsCoveringMap`), and compute a lower bound on $\pi_1(M_n)$ via generators (braid-type loops) surjecting onto $S_n$.
   - Why it might work: it is the mathematically honest path and reuses `Mathlib.Topology.Covering`.
   - Risk: computing $\pi_1$ of a complex hyperplane-arrangement complement is far beyond current Mathlib; likely infeasible now.

### Key Difficulties

- Mathlib lacks fundamental-group computations for hyperplane-arrangement complements; $\pi_1(M_n)$ (a quotient of the braid group) is not available.
- Making "expressible by radicals" precise in the topological setting without silently importing the Galois-theoretic definition (risk of circularity / trivialization).
- The monodromy representation and its surjectivity onto $S_n$ require covering-space transport of paths, which Mathlib supports only partially.

### What Would a Proof Need?

- Key lemma 1: Root-covering and monodromy — the map $M_n$-loops $\to S_n$ is a well-defined surjective homomorphism.
- Key lemma 2: Radical obstruction — a formula using nested $k$-th roots exhibits the monodromy image as a subgroup of an iterated abelian-by-abelian (solvable) group.
- Technical requirements: `Mathlib.GroupTheory.Solvable` (derived series, `not_solvable`), `Mathlib.GroupTheory.SpecificGroups.Alternating` ($A_5$ simple), `Mathlib.Topology.Homotopy.FundamentalGroup`, `Mathlib.Topology.Covering`, and a faithful definition of the discriminant complement building on `abel-ruffini-oq-07-discriminant`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The pure group-theoretic obstruction (Approach A core) is Medium and clearly reachable, since `not_solvable (Equiv.Perm (Fin 5))` and the derived-series API already exist in Mathlib.
- The topological infrastructure (covering of $M_n$, computation of $\pi_1$, surjectivity of monodromy) is genuinely hard: Mathlib has no fundamental-group computations for arrangement complements, so those inputs must start as axioms.
- Comparable formalizations (the Galois Abel-Ruffini in Mathlib) took substantial effort; the topological version is strictly harder on the topology side, hence High / partial-Moonshot on the full statement.

**Estimated Effort**:
- Exploration: 2-4 days to fix the interface and prove the group-theoretic obstruction with topological hypotheses axiomatized.
- If tractable: 2-4 weeks for a faithful axiomatized scaffold with the obstruction lemma proved.
- If hard: unknown (full de-axiomatization of $\pi_1(M_n)$ is a research-level program).

## References

### Papers
- V. I. Arnold (lectures, ~1963–64), recorded in V. B. Alekseev, *Abel's Theorem in Problems and Solutions* (Kluwer, 2004) — the canonical exposition of Arnold's topological proof via monodromy.
- A. Khovanskii, *Topological Galois Theory: Solvability and Unsolvability of Equations in Finite Terms* (Springer, 2014) — the systematic monodromy-group theory extending Arnold's argument.

### Online Resources
- https://en.wikipedia.org/wiki/Abel%E2%80%93Ruffini_theorem — statement and history, including Arnold's topological proof.
- https://www.math.toronto.edu/~arul/ (and various expository notes) — accessible write-ups of the monodromy/commutator argument for the quintic.

### Mathlib
- `Mathlib.GroupTheory.Solvable` — `IsSolvable`, derived series, `not_solvable` for the input contradiction.
- `Mathlib.GroupTheory.SpecificGroups.Alternating` — $A_5$ simple and non-abelian, driving non-solvability of $S_n$, $n \ge 5$.
- `Mathlib.Topology.Homotopy.FundamentalGroup` — `FundamentalGroup`, `π₁`, loop group structure for the monodromy source.
- `Mathlib.Topology.Covering` — `IsCoveringMap` for the root map over the discriminant complement.
- `Mathlib.FieldTheory.AbelRuffini` — the existing Galois-theoretic statement to reconcile with.

## Metadata

```yaml
tags:
  - algebra
  - galois-theory
  - group-theory
  - field-theory
  - topology
  - classic
related_proofs:
  - abel-ruffini
  - abel-ruffini-oq-07-discriminant
  - abel-ruffini-galois-extensions
difficulty: high
source: user-request
created: 2026-07-09T16:57:40-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
