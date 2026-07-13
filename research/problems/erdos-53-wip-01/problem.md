# Problem: Complete the Lean Formalization of Erdős Problem #53 (Sums and Products of Distinct Elements)

**Slug**: erdos-53-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall k \geq 1,\ \exists N_0,\ \forall A \subseteq \mathbb{Z} \text{ finite},\ |A| \geq N_0 \implies \big|\{\textstyle\sum_{a \in S} a : S \subseteq A\} \cup \{\prod_{a \in S} a : \emptyset \neq S \subseteq A\}\big| \geq |A|^k.
$$

Chang (2003) proved this polynomial lower bound for every $k$; Erdős–Szemerédi established the subexponential upper bound $\exp\!\big(c(\log|A|)^2 \log\log|A|\big)$.

### Plain Language

The completion task is to strengthen the work-in-progress Lean 4 formalization of Erdős Problem #53 on sums and products of distinct elements. Given a finite set $A$ of integers, one forms all integers obtainable as a sum of a subset of $A$ or as a product of a subset of $A$. Erdős and Szemerédi (1983) asked whether, for every fixed $k$, a sufficiently large $A$ always produces at least $|A|^k$ such representable integers — the intuition being that additive and multiplicative structure cannot both be sparse. Mei-Chu Chang (2003) proved this affirmatively for all $k$, and Erdős–Szemerédi supplied a matching subexponential upper bound. The current Lean file defines subset sums, subset products, and their union, and states the conjecture and related sum-product conjecture (Problem 52), but Chang's resolution and the upper bound are (or were) carried as axioms. Our goal is to formalize the elementary structural facts and keep Chang's deep theorem cleanly axiomatized.

### Why This Matters

1. **The sum-product phenomenon**: Problem #53 is a clean subset-operation embodiment of the principle that a set cannot be simultaneously additively and multiplicatively structured, one of the central themes of modern additive combinatorics.
2. **A resolved theorem worth verifying honestly**: Chang's 2003 proof settles the problem, so the formalization can aim at `axiomatized` with a clearly stated deep input, while still verifying the many surrounding elementary facts.
3. **Reusable subset-operation machinery**: Formalizing subset sums and products over `Finset.powerset` yields lemmas (e.g. distinct-prime products give $2^{|A|}-1$ values) useful across combinatorial number theory.

## Known Results

### What's Already Proven

- Chang's theorem — for every $k$, sufficiently large finite $A \subseteq \mathbb{Z}$ has at least $|A|^k$ integers representable as subset sums or products (Chang, 2003), via Balog–Szemerédi–Gowers plus multiplicative energy.
- Erdős–Szemerédi upper bound — arbitrarily large sets exist with representable count at most $\exp\!\big(c(\log|A|)^2\log\log|A|\big)$ (Erdős–Szemerédi, 1983).
- Distinct-prime richness — for $A$ a set of distinct primes, unique factorization gives exactly $2^{|A|}-1$ distinct nonempty subset products.

### What's Still Open

- The optimal growth rate of the representable count: is it nearer to polynomial or to $\exp(c(\log|A|)^2)$?
- Whether the result extends to $\mathbb{Z}/p\mathbb{Z}$ or other rings carrying both additive and multiplicative structure.

### Our Goal

Complete the WIP Lean file `Proofs/Erdos53Problem.lean`: formalize the elementary supporting facts as genuine theorems — for distinct primes $|\mathrm{subsetProducts}(A)| = 2^{|A|}-1$ by unique factorization; the union-dominates-each-part monotonicity ($|\mathrm{sumsOrProducts}(A)| \geq |\mathrm{subsetSums}(A)|$ and $\geq |\mathrm{subsetProducts}(A)|$); and small concrete computations of the representable count. Chang's affirmative resolution and the Erdős–Szemerédi upper bound, which are genuinely deep, must remain explicitly axiomatized and disclosed in `assumptions`; the entry stays `axiomatized`, not `verified`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-53 | Parent gallery entry (badge wip): defines `subsetSums`, `subsetProducts`, `sumsOrProducts`, `ErdosProblem53`, and the Problem-52 connection, with Chang's theorem and the upper bound as axioms. | Subset sums/products via `Finset.powerset`, Balog–Szemerédi–Gowers, multiplicative energy |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize the monotonicity and distinct-prime facts as theorems.
   - Why it might work: $\mathrm{sumsOrProducts}(A)$ is by definition the union of the two image sets, so `Finset.card_le_card` on the subset relation gives the dominance lemmas immediately; distinct-prime products follow from `Finset.prod` injectivity under unique factorization.
   - Risk: the injectivity-of-products argument needs care with the empty subset and with `Int` versus `Nat` unique factorization.

2. **Approach B**: Verify small explicit cases of the representable count.
   - Why it might work: For a fixed small $A$, `sumsOrProducts A` is a computable `Finset`, so its cardinality can be evaluated and bounds checked by `decide`.
   - Risk: powerset enumeration grows as $2^{|A|}$, limiting `decide` to very small sets.

### Key Difficulties

- Chang's theorem depends on Balog–Szemerédi–Gowers and multiplicative-energy machinery not available in Mathlib, so it cannot be formalized within scope.
- Handling the empty subset (whose product convention affects `subsetProducts`) requires consistent definitional choices to avoid off-by-one errors.

### What Would a Proof Need?

- Key lemma 1: the union bound $|\mathrm{sumsOrProducts}(A)| \geq \max(|\mathrm{subsetSums}(A)|, |\mathrm{subsetProducts}(A)|)$.
- Key lemma 2: distinct primes give $2^{|A|}-1$ distinct nonempty subset products via unique factorization.
- Technical requirements: `Finset.powerset`, `Finset.image`, `Finset.card_le_card`, and `Nat`/`Int` unique factorization lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The surrounding structural lemmas (monotonicity, distinct-prime products, small computations) are elementary and clearly formalizable, moving the entry from bare axioms toward stated-and-proved supporting results.
- Chang's resolution is a genuinely deep 2003 theorem and stays axiomatized, so the mathematical status of the entry is unchanged.
- Mathlib's `Finset` powerset/image/card API and unique-factorization lemmas cover exactly the tractable parts.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1 week for the monotonicity and distinct-prime lemmas plus small computations
- If hard: unknown for formalizing Chang's theorem or the Erdős–Szemerédi upper bound

## References

### Papers
- P. Erdős and E. Szemerédi, "On sums and products of integers", in Studies in Pure Mathematics, Birkhäuser (1983), 213–218 — introduces the problem and the upper bound.
- M.-C. Chang, "Erdős–Szemerédi problem on sum set and product set", Ann. of Math. 157 (2003), 939–957 — affirmative resolution for all $k$.
- T. Tao and V. Vu, "Additive Combinatorics", Cambridge Univ. Press (2006) — standard reference for sum-product theory.

### Online Resources
- https://erdosproblems.com/53 — canonical statement and resolved status of Problem #53.
- https://erdosproblems.com/52 — the closely related pairwise sum-product conjecture (Problem #52).

### Mathlib
- `Mathlib.Data.Finset.Powerset` — `Finset.powerset` used to define subset sums and products.
- `Mathlib.Algebra.BigOperators.Group.Finset` — `Finset.sum` and `Finset.prod` for the subset operations.

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - additive-combinatorics
  - sum-product
  - subset-sums
  - sidon-related
related_proofs:
  - erdos-53
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
