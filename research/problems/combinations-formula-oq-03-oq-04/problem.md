# Problem: Unimodality of Gaussian (q-)binomial coefficients

**Slug**: combinations-formula-oq-03-oq-04
**Created**: 2026-07-09T16:03:14-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Write the Gaussian binomial coefficient as a polynomial in $q$,
$$
\binom{n}{k}_q \;=\; \sum_{i=0}^{k(n-k)} a_i\, q^i \;\in\; \mathbb{Z}[q],
\qquad a_i \ge 0,
$$
where $a_i$ counts the $k$-element subsets of $\{1,\dots,n\}$ whose element-sum equals $i + \binom{k+1}{2}$ (equivalently, lattice paths from $(0,0)$ to $(n-k,k)$ enclosing area $i$). The claim is that the coefficient sequence $(a_0,\dots,a_{k(n-k)})$ is **symmetric** and **unimodal**:
$$
a_i = a_{\,k(n-k)-i}\quad\text{(symmetry)},
\qquad
a_0 \le a_1 \le \cdots \le a_{\lfloor k(n-k)/2\rfloor} \ge \cdots \ge a_{k(n-k)}\quad\text{(unimodality)}.
$$
The target theorem to formalize in Lean 4 is: for all $n$ and all $0 \le k \le n$, the coefficient sequence of $\binom{n}{k}_q$ is unimodal, i.e. there is no index $i$ with $a_{i-1} > a_i < a_{i+1}$.

### Plain Language

The Gaussian binomial coefficient $\binom{n}{k}_q$ is a polynomial in $q$ whose coefficients are non-negative integers summing to the ordinary binomial coefficient $\binom{n}{k}$. For example $\binom{5}{2}_q = 1 + q + 2q^2 + 2q^3 + 2q^4 + q^5 + q^6$ has coefficient sequence $1,1,2,2,2,1,1$. "Unimodal" means the coefficients rise (weakly) to a single central peak and then fall — they never dip down and come back up. Symmetry (already available in the gallery) says the sequence reads the same forwards and backwards. The problem asks whether the *rising-then-falling* shape can be proved in Lean 4.

### Why This Matters

Symmetry alone is elementary, but unimodality is genuinely deep: it was first proved by Sylvester (1878) and Cayley, and the only fully conceptual proofs known use serious machinery — the $\mathfrak{sl}_2$ representation theory underlying the hard Lefschetz theorem for the cohomology of the complex Grassmannian $\mathrm{Gr}(k,\mathbb{C}^n)$. Formalizing it would (i) give Mathlib a nontrivial unimodality result and a template for "action of $\mathfrak{sl}_2 \Rightarrow$ unimodality" arguments; (ii) connect the gallery's existing division-free q-binomial development to representation theory and algebraic combinatorics; and (iii) exercise Lean's support for polynomial coefficient extraction and log-concavity/unimodality reasoning, which is currently thin.

## Known Results

### What's Already Proven

- **Symmetry** $\binom{n}{k}_q = \binom{n}{n-k}_q$ and coefficient symmetry $a_i = a_{k(n-k)-i}$ — proved in the gallery (`combinations-formula-oq-03`, theorem `qBinom_symm`), over any `CommRing`.
- **Non-negativity of coefficients** — classical (Gauss); the coefficients count subsets/lattice paths by area, hence $a_i \ge 0$.
- **Sylvester's unimodality theorem (1878)** — the coefficient sequence of $\binom{n}{k}_q$ is unimodal; the representation-theoretic proof is due to the $\mathfrak{sl}_2$-action on $\bigoplus \mathbb{C}[\text{partitions in }k\times(n-k)\text{ box}]$.
- **Hard Lefschetz for Grassmannians** — gives unimodality as the statement that cup product with the hyperplane class $[H]^{d-2i}\colon H^{2i} \to H^{2(d-i)}$ is an isomorphism, so the Betti numbers (which are the $a_i$) are unimodal.
- **O'Hara's combinatorial proof (1990)** — an explicit, machine-checkable partition-based decomposition establishing unimodality without representation theory; the most promising route for formalization.

### What's Still Open

- No formalization of Gaussian-binomial unimodality exists in Lean 4 / Mathlib.
- Mathlib has no general "unimodal" predicate for integer sequences, nor the $\mathfrak{sl}_2$-representation / hard-Lefschetz infrastructure needed for the conceptual proof.
- The bridge between the gallery's recurrence-based `qBinom` and its explicit coefficient sequence (as a `Polynomial ℤ` with extractable `coeff i`) has not been formalized.

### Our Goal

Formalize unimodality of the coefficient sequence of $\binom{n}{k}_q$ in Lean 4. Concretely: (1) realize `qBinom (q : Polynomial ℤ) n k` (or a dedicated `Polynomial ℤ`-valued definition) and prove its coefficients agree with the area-enumeration; (2) state a `Unimodal` predicate on the coefficient list; (3) prove unimodality — ideally following O'Hara's combinatorial decomposition, since it avoids the algebraic-topology stack. A tractable first milestone is unimodality for fixed small $k$ (e.g. $k = 2$), where the coefficient formula is explicit.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-03 | Defines `qBinom` over `CommRing`, proves symmetry, q-Pascal, product formula, Vandermonde — the exact objects whose coefficients we must analyze | Division-free q-Pascal recurrence, induction, `linear_combination` certificates |
| combinations-formula | Parent entry: classical $C(n,k)$ and Pascal's identity; $q=1$ specialization gives $\sum_i a_i = C(n,k)$ | `Nat.choose`, Pascal induction |
| partition-theorem | Coefficients $a_i$ count partitions inside a $k\times(n-k)$ box; unimodality is a partition-counting statement | Partition bijections, generating functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — O'Hara's combinatorial decomposition**: Formalize O'Hara's (1990) explicit partition of the coefficient-generating set into symmetric-chain-like pieces, each of which is manifestly unimodal, so the sum is unimodal.
   - Why it might work: purely combinatorial, no representation theory or cohomology; the argument is finite and constructive, a good fit for Lean's `Finset`/partition API.
   - Risk: O'Hara's construction is intricate (nested inductions over partition shapes); getting the bookkeeping to typecheck is substantial work.

2. **Approach B — $\mathfrak{sl}_2$-action / symmetric chain decomposition (SCD)**: Build the raising/lowering operators on the poset $L(k, n-k)$ (partitions in a box, ordered by containment) and derive unimodality from a symmetric chain decomposition (Lindström / de Bruijn–Tengbergen–Kruyswijk style).
   - Why it might work: SCD of $L(k,\ell)$ is a well-studied, explicitly constructible object; unimodality of rank-sizes follows immediately from the existence of an SCD.
   - Risk: constructing an SCD for the general box poset in Lean is itself a research-grade formalization; may be as hard as the target.

3. **Approach C — small-$k$ closed forms first**: For $k=1$, $\binom{n}{1}_q = 1+q+\cdots+q^{n-1}$ (all coefficients 1, trivially unimodal); for $k=2$, derive the explicit coefficient formula and prove unimodality by direct inequality manipulation, then look for a uniform induction.
   - Why it might work: gives concrete, immediately provable milestones and tests the coefficient-extraction infrastructure.
   - Risk: does not obviously generalize to all $k$; may not scale to a uniform proof.

### Key Difficulties

- **Coefficient extraction**: the gallery `qBinom` is defined by recurrence over an abstract `CommRing`. To talk about coefficients we need it as a concrete `Polynomial ℤ` and must prove `coeff i` equals the area-enumeration — a nontrivial bridging lemma.
- **No unimodality API in Mathlib**: `Unimodal` for integer sequences, and the tools to reason about it (single peak, weak monotonicity on either side), must be defined and developed.
- **Depth of the mathematics**: every known proof is nontrivial; the "easy" proofs (hard Lefschetz) require infrastructure Mathlib lacks, and the elementary proofs (O'Hara, SCD) are combinatorially heavy.

### What Would a Proof Need?

- Key lemma 1: a `Polynomial ℤ` realization `gaussPoly n k` with `(gaussPoly n k).coeff i = (number of partitions of i inside the k×(n-k) box)`, tying back to the gallery's `qBinom` via `qBinom_at_one`-style specialization.
- Key lemma 2: a `Unimodal` predicate plus its basic calculus (concatenation, symmetry ⇒ peak location, monotone-then-antitone characterization).
- Key lemma 3 (Approach A/B): either O'Hara's decomposition into unimodal blocks, or an explicit symmetric chain decomposition of the box poset $L(k, n-k)$ with rank-size = $a_i$.
- Technical requirements: robust `Finset` partition/bijection API, comfort with double induction on $(n,k)$, and possibly `decide`/`native_decide` for base cases and small verifications.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is deep (Sylvester 1878; the clean proofs use hard Lefschetz), and the elementary proofs (O'Hara, symmetric chains) are combinatorially intricate.
- Mathlib currently lacks both a unimodality API and the $\mathfrak{sl}_2$/cohomology machinery, so significant scaffolding is required before the main argument.
- However, the objects are concrete and finite, the gallery already supplies `qBinom` and symmetry, and a small-$k$ / O'Hara route offers genuine, checkable milestones — so it is hard but not a moonshot.

**Estimated Effort**:
- Exploration: 1–2 weeks (coefficient-extraction bridge + `Unimodal` API + $k=1,2$ cases)
- If tractable: 1–3 months for a uniform O'Hara-style proof
- If hard: unknown (the representation-theoretic route depends on Mathlib gaining hard-Lefschetz / Grassmannian cohomology, which is a large independent project)

## References

### Papers
- J. J. Sylvester, "Proof of the hitherto undemonstrated fundamental theorem of invariants" (1878) — original proof of unimodality of $\binom{n}{k}_q$.
- K. M. O'Hara, "Unimodality of Gaussian coefficients: a constructive proof" (J. Combin. Theory Ser. A, 1990) — elementary combinatorial proof; the most formalization-friendly route.
- R. P. Stanley, "Log-concave and unimodal sequences in algebra, combinatorics, and geometry" (Ann. NY Acad. Sci., 1989) — survey placing Gaussian-binomial unimodality in context (hard Lefschetz, SCD).
- N. G. de Bruijn, C. Tengbergen, D. Kruyswijk (1951) — symmetric chain decomposition of the divisor/subset lattice, template for the box poset $L(k,\ell)$.
- G. E. Andrews, *The Theory of Partitions* (1976) — partition interpretation of Gaussian coefficients.
- V. Kac, P. Cheung, *Quantum Calculus* (2002) — q-binomial coefficients and the q-Pascal rule.

### Online Resources
- OEIS and standard references on Gaussian binomial coefficient coefficient tables — concrete data for base cases.
- Expository notes on the $\mathfrak{sl}_2$ / hard-Lefschetz proof of unimodality (e.g. Stanley's course notes) — for the conceptual proof.

### Mathlib
- `Mathlib.Data.Nat.Choose.Basic` — ordinary binomial coefficients ($q=1$ specialization target).
- `Mathlib.Combinatorics.Partition` (and `Nat.Partition`) — partitions inside a box; coefficient enumeration.
- `Mathlib.Data.Polynomial.Basic` / `Mathlib.Algebra.Polynomial.Coeff` — `Polynomial ℤ`, `coeff`, degree; needed to realize the coefficient sequence.
- `Mathlib.Order.*` / `Mathlib.Combinatorics.SetFamily.*` — poset and antichain/chain infrastructure for a symmetric-chain-decomposition route.

## Metadata

```yaml
tags:
  - combinatorics
  - q-analogs
  - gaussian-binomial
  - number-theory
  - algebra
  - quantum-groups
  - finite-geometry
related_proofs:
  - combinations-formula-oq-03
  - combinations-formula
  - partition-theorem
difficulty: high
source: user-request
created: 2026-07-09T16:03:14-07:00
```
