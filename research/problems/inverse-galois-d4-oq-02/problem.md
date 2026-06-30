# Problem: Galois Groups of X^n − p over Q for General n and Prime p

**Slug**: inverse-galois-d4-oq-02
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For a prime } p \text{ and } n \ge 1, \text{ let } K = \mathbb{Q}(\sqrt[n]{p}, \zeta_n) \text{ be the splitting field of } X^n - p. \text{ Then under the genericity hypothesis } [\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n) \text{ with } \mathbb{Q}(\sqrt[n]{p}) \cap \mathbb{Q}(\zeta_n) = \mathbb{Q}, \quad \mathrm{Gal}(K/\mathbb{Q}) \cong \mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times, \qquad |\mathrm{Gal}(K/\mathbb{Q})| = n\,\varphi(n).
$$

### Plain Language

The polynomial $X^n - p$ has roots $\zeta_n^k \sqrt[n]{p}$ for $k = 0, \dots, n-1$, where $\sqrt[n]{p}$ is a fixed real $n$-th root of $p$ and $\zeta_n$ is a primitive $n$-th root of unity. Its splitting field is therefore $\mathbb{Q}(\sqrt[n]{p}, \zeta_n)$. A field automorphism is determined by where it sends $\sqrt[n]{p}$ (to another root, i.e. multiply by some $\zeta_n^a$) and where it sends $\zeta_n$ (to a power $\zeta_n^b$ with $\gcd(b,n)=1$). This gives a map $\sigma \mapsto (a, b) \in \mathbb{Z}/n \times (\mathbb{Z}/n)^\times$, and composition makes the group a **semidirect product** $\mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$ — the "affine group" / holomorph-style metacyclic group — of order $n\,\varphi(n)$, *provided* the radical part and the cyclotomic part do not overlap beyond $\mathbb{Q}$. The $n=4$, $p=2$ case is exactly the parent gallery proof: $\mathbb{Z}/4 \rtimes (\mathbb{Z}/4)^\times \cong \mathbb{Z}/4 \rtimes \mathbb{Z}/2 \cong D_4$ of order $4\cdot 2 = 8$.

### Why This Matters

This is a clean, infinite family of explicit non-abelian Galois realizations over $\mathbb{Q}$, directly extending the gallery's Inverse Galois work. Metacyclic groups $\mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$ (and their subgroups) are among the first non-abelian groups one wants to realize for the Inverse Galois Problem, and radical extensions $X^n - p$ are the most accessible source: they need no deep tools beyond Eisenstein irreducibility, cyclotomic degree theory, and a linear-disjointness argument. Formalizing the general order/structure replaces the one-off $D_4$ ($n=4$) and $F_{20}$ ($n=5$) computations with a single uniform theorem, and surfaces exactly where the cyclotomic-radical interaction becomes subtle — the interesting mathematics of the problem.

## Known Results

### What's Already Proven

- $|\mathrm{Gal}(X^4-2/\mathbb{Q})| = 8 \cong D_4$ — gallery proof `inverse-galois-d4` (Proofs/InverseGaloisD4.lean), via Eisenstein lower bound + ℝ-embedding upper bound
- $\mathrm{Gal}(X^5-2/\mathbb{Q}) \cong F_{20} = \mathbb{Z}/5 \rtimes (\mathbb{Z}/5)^\times$ of order 20 — gallery proof `inverse-galois-f20` (analogous degree-5 construction)
- Classical theory: for $p$ prime, $X^n - p$ is irreducible over $\mathbb{Q}$ iff (Vahlen–Capelli) $p$ is not an $\ell$-th power for any prime $\ell \mid n$ and ($4 \nmid n$ or $-4p$... handled), and $\mathrm{Gal}(X^n-a/\mathbb{Q}) \hookrightarrow \mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$ always holds — Lang, *Algebra*, Ch. VI; Jacobson, *Basic Algebra I*

### What's Still Open

- A single Lean theorem giving $|\mathrm{Gal}(X^n-p/\mathbb{Q})| = n\,\varphi(n)$ and the semidirect-product structure for *all* $n$ and primes $p$ under the genericity hypothesis (no such uniform statement is in Mathlib or the gallery)
- The full unconditional "all $n, p$" classification, including every overlap case $\mathbb{Q}(\sqrt[n]{p}) \cap \mathbb{Q}(\zeta_n) \neq \mathbb{Q}$ (e.g. the $4 \mid n$ phenomena where $\sqrt{p}$ or $\sqrt{-p}$ may lie in a cyclotomic field) — genuinely involved, the honest "hard" part of this problem

### Our Goal

Formalize the **order and metacyclic structure for general $n$ under the standard genericity hypotheses** ($X^n-p$ irreducible, $[\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n)$, and $\mathbb{Q}(\sqrt[n]{p})$ linearly disjoint from $\mathbb{Q}(\zeta_n)$ over $\mathbb{Q}$), recovering $n=4 \Rightarrow D_4$ and $n=5 \Rightarrow F_{20}$ as instances. We explicitly do **not** attempt the full unconditional "all $n,p$" theorem — the cyclotomic-overlap cases are deferred and flagged as the remaining hard frontier.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| inverse-galois-d4 | parent: the $n=4$, $p=2$ case ($D_4$, order 8) this work generalizes | Eisenstein irreducibility, ℝ-embedding to bound degree, divisibility antisymmetry |
| inverse-galois-f20 | sibling: the $n=5$, $p=2$ case ($F_{20} = \mathbb{Z}/5 \rtimes \mathbb{Z}/4$, order 20) | splitting-field degree, semidirect-product order $n\varphi(n)$ |
| abel-ruffini-galois-extensions | shared radical-extension / Galois-group-of-$X^n-a$ machinery and solvability structure | tower degrees, cyclotomic adjunction, group-action on roots |
| fourth-root-2-irrational | supplies $\sqrt[n]{p} \notin \mathbb{Q}$ irrationality / minimal-polynomial degree input | Eisenstein, irreducibility of $X^n - p$ |

## Initial Thoughts

### Potential Approaches

1. **Approach A — degree-tower + embedding count**: Prove $[\mathbb{Q}(\sqrt[n]{p}):\mathbb{Q}] = n$ (Eisenstein) and $[\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n)$ (Mathlib cyclotomic), then show the compositum has degree $n\varphi(n)$ using linear disjointness, so $|\mathrm{Gal}| = n\varphi(n)$ since the extension is Galois (splitting field of a separable polynomial).
   - Why it might work: each ingredient already exists in Mathlib (`Polynomial.Gal`, `IsCyclotomicExtension`, `IsGalois`, `finrank` of compositum); generalizes the parent's `Nat.dvd_antisymm` strategy.
   - Risk: proving the compositum degree multiplies (linear disjointness of radical and cyclotomic towers) is the crux and may need a bespoke lemma not in Mathlib.

2. **Approach B — explicit isomorphism to the semidirect product**: Build the homomorphism $\mathrm{Gal} \to \mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$ via the action on $\sqrt[n]{p}$ and $\zeta_n$, prove injectivity from "an automorphism fixing both generators is the identity," then surjectivity/cardinality from Approach A's order count.
   - Why it might work: yields the full group structure (not just order), matching the open question's "computed" and exposing $D_4$, $F_{20}$ as `MulEquiv` instances.
   - Risk: defining the semidirect-product target and the cocycle action cleanly in Lean is fiddly; injectivity needs that the two generators generate the field.

### Key Difficulties

- The overlap case $\mathbb{Q}(\sqrt[n]{p}) \cap \mathbb{Q}(\zeta_n) \neq \mathbb{Q}$ collapses the order below $n\varphi(n)$ (e.g. $\sqrt{p}, \sqrt{-1}, \sqrt{-p}$ landing inside cyclotomic fields when $4 \mid n$); ruling this out / handling it is the hard, genuinely number-theoretic part.
- Irreducibility of $X^n - p$ is *not* automatic for composite $n$ (Vahlen–Capelli criterion: fails when $p$ is a perfect $\ell$-th power for $\ell \mid n$, and a special case at $4 \mid n$); the clean statement needs $n$ of suitable form or the irreducibility taken as a hypothesis.
- Formalizing linear disjointness / "compositum degree is the product" generically in Mathlib for these two specific towers.

### What Would a Proof Need?

- Key lemma 1: $[\mathbb{Q}(\sqrt[n]{p}):\mathbb{Q}] = n$ from Eisenstein irreducibility of $X^n-p$.
- Key lemma 2: $[\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n)$ (Mathlib `IsCyclotomicExtension.finrank` / cyclotomic-polynomial degree).
- Key lemma 3: linear disjointness $\Rightarrow [\mathbb{Q}(\sqrt[n]{p},\zeta_n):\mathbb{Q}] = n\varphi(n)$, hence $|\mathrm{Gal}| = n\varphi(n)$ (`IsGalois.card_aut_eq_finrank`).
- Technical requirements: a `SemidirectProduct` target and the root-action homomorphism for the structural (Approach B) statement; genericity packaged as explicit hypotheses.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The order statement under genericity reuses exactly the parent $D_4$ and sibling $F_{20}$ machinery (already 0-sorry, 0-axiom in the gallery), generalized by parameterizing over $n$ and $p$.
- Similar solved problems: `inverse-galois-d4` ($n=4$) and `inverse-galois-f20` ($n=5$) are full, verified instances — the conceptual path is proven, only the uniform/parametric version remains.
- Mathlib provides `Polynomial.Gal`, `IsGalois`, `IsCyclotomicExtension`, `Polynomial.cyclotomic`, and Eisenstein/`Polynomial.Monic.irreducible` tooling, so most ingredients are available; the linear-disjointness compositum lemma is the main gap.
- The *full* unconditional "all $n,p$" version is harder (Hard/Moonshot) because of the cyclotomic-overlap and irreducibility cases; we deliberately scope to the genericity-hypothesis version.

**Estimated Effort**:
- Exploration: 2–4 days (survey Mathlib cyclotomic + compositum degree API, draft the genericity hypotheses)
- If tractable: 1–3 weeks (order theorem under genericity, then the semidirect-product `MulEquiv`, recovering $D_4$/$F_{20}$)
- If hard: unknown (the unconditional all-$n,p$ classification with overlap cases may remain open in Lean indefinitely)

## References

### Papers
- S. Lang, *Algebra* (3rd ed.), 2002 — Ch. VI on radical extensions, $\mathrm{Gal}(X^n-a)$ embedding into $\mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$, and cyclotomic theory
- N. Jacobson, *Basic Algebra I* (2nd ed.), 1985 — Galois groups of binomials $X^n - a$ and the Vahlen–Capelli irreducibility criterion

### Online Resources
- https://en.wikipedia.org/wiki/Inverse_Galois_problem — overview of which groups are known to be realizable over $\mathbb{Q}$
- https://en.wikipedia.org/wiki/Casus_irreducibilis — and the metacyclic/affine-group structure of $\mathrm{Gal}(X^n-a)$ (binomial/radical extensions)

### Mathlib
- Mathlib.FieldTheory.PolynomialGaloisGroup (`Polynomial.Gal`) — the Galois group of a polynomial as `f.Gal`
- Mathlib.FieldTheory.Galois.Basic (`IsGalois`, `IsGalois.card_aut_eq_finrank`) — Galois extensions and the order = degree identity
- Mathlib.NumberTheory.Cyclotomic.Basic / Mathlib.RingTheory.Polynomial.Cyclotomic.Basic (`IsCyclotomicExtension`, `Polynomial.cyclotomic`) — degree $\varphi(n)$ of $\mathbb{Q}(\zeta_n)$
- Mathlib.GroupTheory.SemidirectProduct (`SemidirectProduct`) — target group $\mathbb{Z}/n \rtimes (\mathbb{Z}/n)^\times$ for the structural statement

## Metadata

```yaml
tags:
  - algebra
  - galois-theory
  - inverse-galois-problem
  - cyclotomic-fields
  - radical-extensions
related_proofs:
  - inverse-galois-d4
  - inverse-galois-f20
  - abel-ruffini-galois-extensions
difficulty: medium
source: user-request
created: 2026-06-27T11:33:01-07:00
```
