# Problem: Degree-4 Newton Identity

**Slug**: newton-power-sum-identities-oq-01-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
p_4 = e_1^4 - 4 e_1^2 e_2 + 4 e_1 e_3 + 2 e_2^2 - 4 e_4,
$$

where $p_k = \sum_i x_i^k$ are the power sums and $e_k$ the elementary symmetric
polynomials, obtained by unrolling Newton's identity
$p_k = e_1 p_{k-1} - e_2 p_{k-2} + e_3 p_{k-3} - 4 e_4$ (with $p_0 = n$, $e_j = 0$ for $j > n$).

### Plain Language

The gallery entry proves Newton's power-sum identities up to degree 3, expressing
$p_1, p_2, p_3$ in the elementary symmetric polynomials. This problem extends the
pattern one step: derive the degree-4 closed form for $p_4$ by the same unrolling of
Newton's recurrence, and state it uniformly.

### Why This Matters

Degree 4 is the first case where the "square" term $2e_2^2$ appears alongside the
mixed terms, so it is the natural test of a uniform closed-form statement of the
Newton identities and a stepping stone toward the reverse (Girard–Newton) direction
expressing $e_k$ in the $p_i$.

## Known Results

### What's Already Proven

- Newton's recurrence $p_k = \sum_{i=1}^{k-1}(-1)^{i-1} e_i p_{k-i} + (-1)^{k-1} k e_k$ — Mathlib `MvPolynomial.psum` / `Multiset` symmetric-function API.
- Degrees 1–3 closed forms — parent entry `newton-power-sum-identities-oq-01`.

### What's Still Open

- The explicit degree-4 closed form as a verified identity in the gallery.
- A uniform statement covering degrees $\le 4$.

### Our Goal

Formalize $p_4 = e_1^4 - 4 e_1^2 e_2 + 4 e_1 e_3 + 2 e_2^2 - 4 e_4$ over a commutative
ring (or `MvPolynomial (Fin n) ℤ` with $n \ge 4$), reusing the parent's degrees 1–3.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| newton-power-sum-identities-oq-01 | Parent: degrees 1–3 Newton identities | symmetric functions, recurrence |
| newton-power-sum-identities-oq-01-oq-02 | Sibling entry in the same vein | psum/esymm algebra |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Unroll Newton's recurrence symbolically.
   - Why it might work: substitute the degree-3 result into $p_4 = e_1 p_3 - e_2 p_2 + e_3 p_1 - 4 e_4$ and `ring`.
   - Risk: sign/coefficient conventions in Mathlib's Newton-identity statement.

2. **Approach B**: Prove directly in `MvPolynomial (Fin 4) ℤ` by `decide`/`ring` after `psum`/`esymm` unfolding.
   - Why it might work: fully concrete, no recurrence needed for a fixed variable count.
   - Risk: term blow-up; may need `MvPolynomial.funext` or evaluation on generic points.

### Key Difficulties

- Matching Mathlib's exact sign convention for Newton's identities.
- Keeping the $e_j = 0$ (for $j > n$) truncation correct if working with fixed $n$.

### What Would a Proof Need?

- Key lemma 1: parent's degree-3 identity $p_3 = e_1^3 - 3e_1 e_2 + 3 e_3$.
- Key lemma 2: Newton's recurrence at $k=4$.
- Technical requirements: `ring`, `MvPolynomial.esymm`/`psum` lemmas.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- [Reason for assessment] Mechanical one-step extension of an existing verified entry.
- [Similar problems that have been solved] Degrees 1–3 already formalized in the parent.
- [Techniques available in Mathlib] `MvPolynomial.esymm`, `psum`, Newton-identity lemmas, `ring`.

**Estimated Effort**:
- Exploration: hours
- If tractable: hours to a day
- If hard: n/a

## References

### Papers
- Macdonald, *Symmetric Functions and Hall Polynomials*, 1995 — Newton's identities.

### Online Resources
- https://en.wikipedia.org/wiki/Newton%27s_identities — degree-by-degree table.

### Mathlib
- `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` — Newton's identities in Mathlib.

## Metadata

```yaml
tags:
  - algebra
  - symmetric-functions
  - newton-identities
related_proofs:
  - newton-power-sum-identities-oq-01
  - newton-power-sum-identities-oq-01-oq-02
difficulty: low
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
