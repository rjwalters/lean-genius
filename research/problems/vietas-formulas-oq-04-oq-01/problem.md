# Problem: Cubic Discriminant as Product of Squared Root-Gaps

**Slug**: vietas-formulas-oq-04-oq-01
**Created**: 2026-07-02T01:25:36-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a depressed cubic $x^3 + px + q$ with roots $r_1, r_2, r_3$,
$$
\Delta = \prod_{i<j} (r_i - r_j)^2 = -4p^3 - 27q^2 .
$$

### Plain Language

The discriminant of a cubic measures how "spread out" its roots are: it is the product of the squared
differences of all pairs of roots. We want to prove that for the depressed cubic $x^3+px+q$ this
symmetric-function expression $\prod_{i<j}(r_i-r_j)^2$ equals the classical closed form
$-4p^3 - 27q^2$, and that it vanishes exactly when the cubic has a repeated root.

### Why This Matters

The discriminant is the fundamental invariant detecting repeated roots and, over $\mathbb{R}$, the
sign that separates one-real-root from three-real-root cubics. Deriving $\prod(r_i-r_j)^2 = -4p^3-27q^2$
from Vieta's relations demonstrates the power-sum / elementary-symmetric machinery of the parent and
sets the template for the general degree-$n$ discriminant = squared Vandermonde determinant (siblings
oq-02, oq-03).

## Known Results

### What's Already Proven

- Vieta's formulas relating coefficients to elementary symmetric functions of the roots — parent family `vietas-formulas` and `vietas-formulas-oq-03-oq-03` (Newton's identities for the roots, verified).
- For the depressed cubic: $e_1 = r_1+r_2+r_3 = 0$, $e_2 = \sum_{i<j} r_i r_j = p$, $e_3 = r_1r_2r_3 = -q$.
- Mathlib `Polynomial.roots`, `MvPolynomial.esymm`, `Polynomial.discriminant` (where available), and `aeval` transport used in `vietas-formulas-oq-03-oq-03`.

### What's Still Open

- The explicit identity $\prod_{i<j}(r_i-r_j)^2 = -4p^3 - 27q^2$ for the depressed cubic, in Lean.
- Its corollary: $\Delta = 0 \iff$ the cubic has a repeated root.

### Our Goal

Prove $\prod_{i<j}(r_i-r_j)^2 = -4p^3 - 27q^2$ over a commutative ring (or field) by expanding the
symmetric product in terms of $e_1=0, e_2=p, e_3=-q$ via Newton's identities / power sums, then
`ring`-normalizing. Verify the classical special case and the vanishing-iff-repeated-root corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| vietas-formulas-oq-03-oq-03 | Sibling: Newton's identities for the roots via `aeval` transport | power sums, elementary symmetric polynomials |
| vietas-formulas-oq-04 | Direct parent: discriminant open questions | Vieta relations, symmetric functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Symmetric-function expansion via Vieta.
   - Why it might work: $\prod_{i<j}(r_i-r_j)^2$ is symmetric, so it is a polynomial in $e_1,e_2,e_3$; substituting $e_1=0, e_2=p, e_3=-q$ and normalizing with `ring` gives $-4p^3-27q^2$.
   - Risk: expressing the symmetric product in the $e_i$ basis explicitly (needs Newton's identities or a direct expansion).

2. **Approach B**: Direct computation with three named roots plus Vieta constraints.
   - Why it might work: introduce $r_1,r_2,r_3$, impose $r_1+r_2+r_3=0$, and let `ring`/`linear_combination` discharge the polynomial identity using the constraints.
   - Risk: requires eliminating one root via the sum-zero relation; `ring` may need the substitution done by hand.

### Key Difficulties

- Getting from the pairwise-difference product to a polynomial in $p,q$ cleanly — the intermediate expansion has many terms.
- Working over `Polynomial.roots` (a multiset) vs. three explicit named roots; choosing the representation that `ring` handles.

### What Would a Proof Need?

- Key lemma 1: $\prod_{i<j}(r_i-r_j)^2$ expressed via power sums / $e_i$ (either Newton's identities or an explicit degree-6 symmetric expansion).
- Key lemma 2: Vieta substitution $e_1=0, e_2=p, e_3=-q$ for the depressed cubic.
- Technical requirements: `ring`, `linear_combination`, `MvPolynomial.esymm` or explicit roots; optionally `Polynomial.discriminant`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- [Reason for assessment] With three explicit roots and the sum-zero constraint, this is a finite polynomial identity that `ring`/`linear_combination` can close once set up.
- [Similar problems that have been solved] Sibling oq-03-oq-03 (Newton's identities for the roots) shows the exact `aeval`/symmetric-function transport needed.
- [Techniques available in Mathlib] `ring`, `linear_combination`, `MvPolynomial.esymm`, `Polynomial.roots`.

**Estimated Effort**:
- Exploration: 0.5 day
- If tractable: 1–3 days
- If hard: unknown

## References

### Papers
- D. A. Cox, "Galois Theory" — discriminants of polynomials and their symmetric-function formulas.

### Online Resources
- https://en.wikipedia.org/wiki/Discriminant#Degree_3 — the $-4p^3-27q^2$ formula for the depressed cubic.

### Mathlib
- `Mathlib.RingTheory.Polynomial.Vieta` and `Mathlib.RingTheory.Discriminant` — Vieta relations and discriminant infrastructure.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - discriminant
related_proofs:
  - vietas-formulas-oq-03-oq-03
  - vietas-formulas-oq-04
difficulty: medium
source: gallery-gap
created: 2026-07-02T01:25:36-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
