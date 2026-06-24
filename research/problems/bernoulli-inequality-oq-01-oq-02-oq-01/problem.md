# Problem: Degree-k Binomial Truncation Lower Bound for (1+a)ⁿ

**Slug**: bernoulli-inequality-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall a\ge 0,\ \forall n,k\in\mathbb{N}:\quad 1+\sum_{j=1}^{k}\binom{n}{j}a^{j}\ \le\ (1+a)^{n},\quad\text{with equality}\iff a=0\ \lor\ n\le k.
$$

### Plain Language

Bernoulli's inequality 1 + na ≤ (1+a)ⁿ is the k = 1 case of a family: truncating the binomial expansion of (1+a)ⁿ after the degree-k term gives a lower bound for all a ≥ 0, because every dropped term C(n,j)aʲ (j > k) is nonnegative. This open question asks to formalize the general degree-k truncation 1 + Σ_{j≤k} C(n,j)aʲ ≤ (1+a)ⁿ together with the sharp equality characterization: equality holds iff a = 0 (all higher terms vanish) or n ≤ k (no higher terms exist). The parent suggests a uniform Pascal-style induction.

### Why This Matters

- Generalizes Bernoulli's inequality into a whole tower of polynomial lower bounds, with k=1 recovering the classical statement and larger k giving successively tighter bounds.
- The equality case (a=0 ∨ n≤k) is the interesting refinement — it pins down exactly when truncation is exact, which the plain inequality does not.
- Mathlib has add_pow (binomial theorem), Finset.sum, and Nat.choose; the bound is a Finset.sum_le_sum over the nonnegative tail, so it is well-supported.

## Known Results

### What's Already Proven

- Parent bernoulli-inequality-oq-01-oq-02 (verified, 0-axiom): the degree-k binomial truncation viewpoint of Bernoulli's inequality.
- Mathlib: add_pow / Commute.add_pow giving (1+a)ⁿ = Σ_{j=0}^{n} C(n,j) aʲ.
- Mathlib: Finset.sum_le_sum, Finset.sum_range_succ, nonnegativity of aʲ for a≥0.

### What's Still Open

- Q1: Prove the inequality 1 + Σ_{j∈range(k+1), j≥1} C(n,j) aʲ ≤ (1+a)ⁿ for a≥0, by writing (1+a)ⁿ via add_pow and bounding below by the degree-≤k partial sum (the tail j>k is nonnegative).
- Q2: Prove equality ⟺ a=0 ∨ n≤k: if n≤k the partial sum is the whole sum; if a>0 and n>k the term C(n,k+1)a^{k+1}>0 is strictly dropped.
- Q3 (stretch): derive Bernoulli (k=1) and the quadratic refinement 1+na+C(n,2)a² ≤ (1+a)ⁿ as named corollaries.

### Our Goal

Formalize the degree-k binomial truncation lower bound for (1+a)ⁿ with a≥0 and its sharp equality characterization (a=0 ∨ n≤k), verified/0-axiom.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bernoulli-inequality-oq-01-oq-02 | parent open question | source of this extension |
| bernoulli-inequality | ancestor in the same family | shared definitions and lemmas |
| bernoulli-inequality-oq-01 | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Binomial theorem + nonnegative tail**: Expand (1+a)ⁿ=Σ_{j=0}^{n} C(n,j)aʲ via add_pow; the degree-≤min(k,n) head is the claimed sum, the tail terms are ≥0, so Finset.sum_le_sum gives the bound.
   - Risk: Index alignment between range(k+1) and range(n+1), and the min(k,n) split for the head.
2. **Pascal induction on n**: Induct on n using C(n+1,j)=C(n,j)+C(n,j-1) and (1+a)^{n+1}=(1+a)(1+a)ⁿ, as the parent hints.
   - Risk: The induction must carry the equality case; bookkeeping is heavier than the direct expansion.

### Key Difficulties

- Cleanly splitting Σ_{j=0}^{n} into the degree-≤k head and the nonnegative tail (handle n≤k vs n>k).
- Strictness in the equality case: exhibiting one strictly-positive dropped term when a>0 and n>k.

### What Would a Proof Need?

- add_pow expansion of (1+a)ⁿ.
- Finset.sum_le_sum with nonneg tail; a^j ≥ 0 for a ≥ 0.
- A strict-positivity lemma for the equality direction.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Researchers have shipped adjacent bernoulli-family OQ entries verified/0-axiom (e.g. line-escapes-bounded-power).
- The inequality is a direct Finset.sum_le_sum once add_pow is invoked; the equality case is the only subtle part.
- All Mathlib APIs (add_pow, Nat.choose, Finset.sum) are stable at v4.26.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- G. H. Hardy, J. E. Littlewood, G. Pólya, Inequalities (1934) §2 — Bernoulli and binomial inequalities.
- D. S. Mitrinović, Analytic Inequalities (1970) — Bernoulli-type inequalities.

### Online Resources
- https://en.wikipedia.org/wiki/Bernoulli%27s_inequality
- https://en.wikipedia.org/wiki/Binomial_theorem

### Mathlib
- Mathlib.Algebra.BigOperators.NatAntidiagonal / Mathlib.Algebra.GroupPower — add_pow
- Mathlib.Algebra.Order.BigOperators — Finset.sum_le_sum
- Mathlib.Data.Nat.Choose.Basic — Nat.choose, Pascal recurrence

## Metadata

```yaml
tags:
  - seeker-selected
  - analysis
  - inequality
  - bernoulli-inequality
  - binomial-theorem
  - equality-case
  - induction
related_proofs:
  - bernoulli-inequality
  - bernoulli-inequality-oq-01
  - bernoulli-inequality-oq-01-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-06-24
```
