# Problem: Newton's Identities via Mathlib's Polynomial.Vieta

**Slug**: vietas-formulas-oq-03-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a monic polynomial $P(X) = \prod_{i=1}^{n} (X - r_i)$ with roots $r_1,\dots,r_n$ in a
commutative ring, state and prove Newton's identities relating the power sums
$p_k = \sum_i r_i^k$ to the elementary symmetric polynomials $e_k = e_k(r_1,\dots,r_n)$
(equivalently, to the coefficients of $P$ via Vieta):

$$
p_k - e_1 p_{k-1} + e_2 p_{k-2} - \cdots + (-1)^{k-1} e_{k-1} p_1 + (-1)^{k} k\,e_k = 0
\qquad (1 \le k \le n),
$$

with the coefficients $e_j$ read off $P$ through Mathlib's `Polynomial.Vieta`
(`Multiset.prod_X_sub_C_coeff` / `Polynomial.coeff_eq_esymm_roots_of_...`).

### Plain Language

The parent's sibling `vietas-formulas-oq-03-oq-01` proved Newton's identities abstractly
for $n$ variables using `MvPolynomial.esymm` and power sums. This child *bridges* that
abstract symmetric-function statement to concrete polynomial coefficients: given an actual
polynomial, its coefficients (up to sign) are the elementary symmetric polynomials of its
roots (Vieta), so Newton's identities become a statement about coefficients and root power sums.

### Why This Matters

Connecting the abstract `MvPolynomial.esymm` identities to Mathlib's `Polynomial.Vieta`
makes Newton's identities usable for concrete polynomials (e.g. computing $\sum r_i^k$ from
coefficients — the basis of the Faddeev–LeVerrier characteristic-polynomial algorithm).

## Known Results

### What's Already Proven

- Sibling `vietas-formulas-oq-03-oq-01`: general-$n$ Newton identities in `MvPolynomial.esymm`/psum form.
- Parent `vietas-formulas-oq-03`: low-degree Vieta/Newton relations.
- Mathlib `Polynomial.Vieta` (`Multiset.prod_X_sub_C_coeff`, `Polynomial.coeff_eq_esymm...`),
  `MvPolynomial.esymm`, `MvPolynomial.psum`, and `Mathlib` Newton's-identity lemmas
  (`MvPolynomial.psum_eq_sum_esymm` / `mul_esymm_eq_sum` if present).

### What's Still Open (in this child)

- A statement of Newton's identities for the roots of a *given* `Polynomial R` (as a `Multiset` of roots),
  with coefficients supplied by `Polynomial.Vieta`.
- The bridge lemma: `P.coeff (n-k) = (-1)^k * e_k(roots)` for a monic split polynomial.

### Our Goal

Instantiate the abstract Newton identities at the multiset of roots of a monic polynomial
and rewrite the $e_k$ via `Polynomial.Vieta`, obtaining Newton's identities expressed in the
polynomial's coefficients. Restrict to a splitting field / `Multiset` of roots to keep it concrete.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| vietas-formulas-oq-03-oq-01 | abstract general-$n$ Newton identities | `MvPolynomial.esymm`, psum |
| vietas-formulas-oq-03 | parent: low-degree Vieta | coefficient/root relations |
| newton-power-sum-identities-oq-01 | power-sum unrolling (degree 3,4) | recurrence expansion |

## Initial Thoughts

### Potential Approaches

1. **Reuse the sibling's `esymm`/`psum` identity, then bridge**: apply the general Newton
   identity to the multiset of roots, then rewrite each `esymm` as a coefficient of $P$ via
   `Polynomial.Vieta` (`Multiset.prod_X_sub_C_coeff`).
   - Why it might work: both halves already exist in Mathlib / the sibling entry; this is glue.
   - Risk: reconciling `MvPolynomial.esymm` (over `Fin n` variables) with `Multiset.esymm`
     (over a multiset of roots) — need the `esymm` transfer lemma.

2. **Direct generating-function proof**: from $P'(X)/P(X) = \sum_i 1/(X-r_i) = \sum_k p_k X^{-k-1}$
   and $P(X) = \sum (-1)^j e_j X^{n-j}$, compare coefficients of $P'(X) = (\log P)' P$.
   - Why it might work: gives all identities at once (the OQ's suggested log-derivative route).
   - Risk: formal Laurent/power-series bookkeeping in Lean is heavier.

### Key Difficulties

- Transferring between `MvPolynomial.esymm` (indexed variables) and `Multiset.esymm` (roots).
- Working over a field where $P$ splits, or phrasing everything on the `Multiset` of roots directly.

### What Would a Proof Need?

- The bridge `Multiset.esymm (roots P) = ± P.coeff ...` from `Polynomial.Vieta`.
- The Newton identity in `Multiset.esymm`/`Multiset.psum` form (or the transfer from the sibling).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The abstract identity and the Vieta bridge both exist; the work is the transfer lemma + glue.
- Risk concentrated in `MvPolynomial` ↔ `Multiset` symmetric-function reconciliation.

**Estimated Effort**:
- Exploration: 0.5–1 day (locating exact Mathlib `esymm`/Vieta lemmas)
- If tractable: 2–4 days

## References

### Mathlib
- `Polynomial.Vieta`, `Multiset.prod_X_sub_C_coeff` — coefficients as elementary symmetric functions.
- `MvPolynomial.esymm`, `MvPolynomial.psum`, Newton's-identity lemmas.

## Metadata

```yaml
tags:
  - algebra
  - symmetric-functions
  - polynomial
  - vieta
  - newton-identities
related_proofs:
  - vietas-formulas-oq-03-oq-01
  - newton-power-sum-identities-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
