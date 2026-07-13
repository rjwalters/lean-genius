# Problem: Dual Newton–Girard — express eₖ as polynomials in the power sums p₁,…,pₖ

**Slug**: amgm-inequality-oq-02-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Over a ℚ-algebra, invert the Newton–Girard recurrence to obtain the elementary symmetric polynomials `eₖ` as polynomials in the power sums `p₁,…,pₖ`:
$$
e_k \;=\; \frac{1}{k!}\,
\det\!\begin{pmatrix}
p_1 & 1 & 0 & \cdots & 0\\
p_2 & p_1 & 2 & \cdots & 0\\
\vdots & & \ddots & & \vdots\\
p_{k-1} & p_{k-2} & \cdots & p_1 & k-1\\
p_k & p_{k-1} & \cdots & p_2 & p_1
\end{pmatrix},
\qquad\text{equivalently}\qquad
k\,e_k \;=\; \sum_{i=1}^{k} (-1)^{i-1} e_{k-i}\, p_i .
$$

### Plain Language

The parent proves the full Newton–Girard recurrence relating the power sums `pₖ = Σ xⱼᵏ` to the elementary symmetric polynomials `eₖ`. Read one way, the recurrence computes `pₖ` from `e₁,…,eₖ`. This leaf asks for the **dual** direction: solve the same recurrence for `eₖ` in terms of `p₁,…,pₖ`, yielding the determinant ("Newton's identities, inverse form") and the equivalent solved recurrence `k·eₖ = Σ (-1)^{i-1} e_{k-i} pᵢ`.

### Why This Matters

The two directions of Newton–Girard are the bridge between the multiplicative invariants (`eₖ`, the coefficients of `∏(X - xⱼ)`) and the additive invariants (`pₖ`, traces of powers). Having both directions formalized makes the change of basis between symmetric-function bases fully usable — e.g. recovering a characteristic polynomial from traces of matrix powers (Faddeev–LeVerrier is the same identity), which already appears elsewhere in the gallery.

## Known Results

### What's Already Proven

- Parent `amgm-inequality-oq-02-oq-01-oq-01`: the full Newton–Girard recurrence over any number of variables (power sums from elementary symmetrics).
- Mathlib: `MvPolynomial.esymm`, `MvPolynomial.psum`, `MvPolynomial.psum_eq_sum_esymm` / `MvPolynomial.esymm_to_psum`-style identities, `Mathlib/RingTheory/MvPolynomial/NewtonIdentities.lean`.

### What's Still Open

- The solved/dual form: `eₖ` as an explicit polynomial in `p₁,…,pₖ` (recurrence and/or determinant), over a ℚ-algebra (division by `k!` requires invertibility of integers).

### Our Goal

Prove `k · eₖ = Σ_{i=1}^{k} (-1)^{i-1} e_{k-i} pᵢ` (a direct rearrangement of the parent's Newton identity), then solve it downward over a `ℚ`-algebra to express each `eₖ` as a polynomial in `p₁,…,pₖ`; optionally package the determinant form.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `amgm-inequality-oq-02-oq-01-oq-01` | parent: full Newton–Girard recurrence | `MvPolynomial.esymm`, `psum` |
| `cayley-hamilton`-family / Faddeev–LeVerrier entries | same identity for char-poly from traces | symmetric functions |

## Initial Thoughts

### Potential Approaches

1. **Rearrange the parent's identity**: Mathlib's `NewtonIdentities` gives the alternating sum `Σ (-1)^i e_i p_{k-i}`-type relation; isolate the `eₖ` term to get `k·eₖ = Σ_{i≥1} (-1)^{i-1} e_{k-i} pᵢ`.
   - Why it might work: it is an algebraic rearrangement, no new mathematics.
   - Risk: index/sign alignment with Mathlib's exact statement of the Newton identities.

2. **Strong induction for the closed polynomial**: define `e'ₖ : MvPolynomial … ℚ` by the solved recurrence and prove `e'ₖ = esymm k` by induction using the rearranged identity and invertibility of `k` in ℚ.
   - Why it might work: division by `k` is legal over ℚ; the recurrence is triangular.
   - Risk: managing the `ℚ`-algebra coercions and `Nat` casts cleanly.

### Key Difficulties

- Division by `k!` / `k` forces the ℚ-algebra (or `CharZero`) hypothesis — must be threaded carefully.
- Sign and index conventions in Mathlib's `NewtonIdentities`.

### What Would a Proof Need?

- Key lemma 1: solved recurrence `k·eₖ = Σ_{i=1}^k (-1)^{i-1} e_{k-i} pᵢ` from the parent/Mathlib identity.
- Key lemma 2: `eₖ` as an explicit polynomial in `p₁,…,pₖ` (induction).
- (Optional) Key lemma 3: the determinant form.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already has the Newton identities; this is largely a rearrangement + induction.
- Parent is verified and 0-axiom; reuse its `esymm`/`psum` setup.
- The determinant packaging is optional polish.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days (solved recurrence + closed polynomial form)
- If hard: the full determinant identity with clean statement

## References

### Papers
- I. G. Macdonald, *Symmetric Functions and Hall Polynomials* — Newton's identities, both directions.

### Online Resources
- Standard references on Newton's identities / power-sum ↔ elementary symmetric change of basis.

### Mathlib
- `Mathlib/RingTheory/MvPolynomial/NewtonIdentities.lean` — Newton's identities.
- `Mathlib/RingTheory/MvPolynomial/Symmetric.lean` — `esymm`, `psum`.

## Metadata

```yaml
tags:
  - algebra
  - symmetric-polynomials
  - newton-girard
  - power-sums
  - elementary-symmetric-polynomials
related_proofs:
  - amgm-inequality-oq-02-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
