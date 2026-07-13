# Problem: Complete Erdős Problem #241 — Maximum Size of B₃ Sets

**Slug**: erdos-241-wip-01
**Created**: 2026-07-09T19:15:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
f(N) := \max\Big\{ |A| : A \subseteq \{1,\dots,N\},\ \text{all sums } a_1+a_2+a_3\ (a_i \in A,\ a_1\le a_2\le a_3)\ \text{distinct} \Big\}
$$

**Question:** is $f(N) \sim N^{1/3}$ as $N \to \infty$? (A set with all three-element sums distinct is called a $B_3$ set.)

### Plain Language

A $B_3$ set is a set of integers in which every unordered triple has a distinct sum — no two different triples add to the same value. We want the largest such subset of $\{1,\dots,N\}$. Trivially there are about $N^{1/3}$ elements achievable, and no more than a constant times $N^{1/3}$; the question is whether the constant is exactly $1$, i.e. whether $f(N)/N^{1/3} \to 1$.

### Why This Matters

$B_3$ sets are the degree-3 generalization of Sidon ($B_2$) sets, central objects in additive combinatorics. Pinning down the constant tests how sharp our upper-bound machinery (Fourier/moment methods) is against algebraic constructions. Erdős attached a **\$100 prize** to closing the gap, linking finite-field constructions, additive energy, and analytic number theory.

## Known Results

### What's Already Proven

- **Bose–Chowla (1962):** explicit $B_3$ sets of size $(1+o(1))N^{1/3}$ via the cubing map in $\mathbb{F}_{p^3}$ — a matching *lower* bound.
- **Upper bound:** $f(N) \le (1.519\ldots + o(1))N^{1/3}$ (Green and later refinements), still above the conjectured constant $1$.
- Gallery entry `erdos-241` formalizes the $B_3$ definition and the lower-bound framing in Lean.

### What's Still Open

- Whether the true constant is $1$ (i.e. $f(N) \sim N^{1/3}$) — the main conjecture.
- Closing the gap between the constructive constant $1$ and the analytic constant $\approx 1.519$.

### Our Goal

Complete the WIP gallery formalization `erdos-241`: formalize the $B_3$ predicate, the Bose–Chowla lower-bound construction (or its counting core), and state the asymptotic conjecture as a formal proposition. Discharge remaining scaffolding `sorry`s where the mathematics is settled.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-241 | Base WIP entry this problem completes | $B_3$ definition, additive combinatorics |
| erdos-350 | Sidon / dissociated sets (neighbor) | additive combinatorics |

## Initial Thoughts

### Potential Approaches

1. **Formalize the counting core**: prove the distinct-triple-sums condition forces $\binom{|A|}{3} \lesssim$ (number of possible sums) $\approx 3N$, yielding $f(N) = O(N^{1/3})$.
   - Why it might work: elementary double counting, expressible with `Finset` reasoning.
   - Risk: the *sharp* constant needs Fourier-analytic input beyond elementary counting.

2. **Formalize Bose–Chowla lower bound**: construct the $\mathbb{F}_{p^3}$ set and prove the $B_3$ property from injectivity of cubing.
   - Why it might work: algebraic, self-contained; Mathlib has finite-field infrastructure.
   - Risk: transferring the finite-field set back to $\{1,\dots,N\}$ with size control is technical.

### Key Difficulties

- The sharp upper constant is genuinely open — only the $O(N^{1/3})$ order is provable elementarily.
- Finite-field-to-integer transfer requires careful size/injectivity bookkeeping.

### What Would a Proof Need?

- Key lemma 1: injectivity of $x \mapsto x^3$ giving distinct triple sums in $\mathbb{F}_{p^3}$.
- Key lemma 2: double-counting bound $\binom{|A|}{3} \le \#\{\text{possible sums}\}$.
- Technical requirements: Mathlib `Finset`, `ZMod`, finite-field cardinality lemmas.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The sharp asymptotic constant is an open, prize problem.
- The order-of-magnitude bounds ($\Theta(N^{1/3})$) are formalizable and a realistic completion target.
- Mathlib supports finite fields and `Finset` double counting.

**Estimated Effort**:
- Exploration: days
- If tractable (order bounds + construction): weeks
- If hard (sharp constant): unknown

## References

### Papers
- R. C. Bose, S. Chowla, "Theorems in the additive theory of numbers" (1962) — $B_h$ constructions.
- K. O'Bryant, "A complete annotated bibliography of work related to Sidon sets."
- B. Green, upper bounds for $B_3$ sets.

### Online Resources
- Erdős Problems database, Problem #241 — https://www.erdosproblems.com/241

### Mathlib
- `Mathlib.FieldTheory.Finite.Basic` — finite fields for Bose–Chowla.
- `Mathlib.Combinatorics.Additive` / `Mathlib.Data.Finset.Card` — additive/counting tools.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - sidon-sets
  - b3-sets
  - number-theory
related_proofs:
  - erdos-241
  - erdos-350
difficulty: high
source: proof-suggestion
created: 2026-07-09T19:15:58-07:00
```
