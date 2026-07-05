# Problem: Moments of the standard normal — E[X^{2k}] = (2k−1)!! and E[X^{2k+1}] = 0

**Slug**: area-of-circle-oq-05-incomplete-01-oq-01
**Created**: 2026-07-02T02:47:20-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a standard normal variable `X` with density `φ(x) = (1/√(2π)) e^{−x²/2}`:

$$
\mathbb{E}[X^{2k}] = (2k-1)!! = 1 \cdot 3 \cdot 5 \cdots (2k-1), \qquad \mathbb{E}[X^{2k+1}] = 0.
$$

Formalize the even and odd moments of the standard normal distribution, obtained from the Gaussian
normalization by repeated integration by parts against the normalized density; the odd moments
vanish by symmetry (odd integrand over a symmetric domain).

### Plain Language

The parent chain reaches the Gaussian integral `∫ e^{−x²/2} dx = √(2π)` (the normalization behind
`area-of-circle-oq-05-incomplete-01`). Once you have the normalized density, its moments follow a
clean pattern: even moments are double factorials `(2k−1)!! = 1·3·5···(2k−1)` and odd moments are
zero. The proof is the standard recursion `E[X^{2k}] = (2k−1) E[X^{2k−2}]` from integration by
parts (differentiating `x^{2k−1}`, integrating `x e^{−x²/2}`), with the odd case killed by symmetry.

### Why This Matters

The Gaussian moments are foundational in probability, statistics, and physics (they underlie the
Wick/Isserlis theorem and the moment-generating function of the normal). Formalizing them turns the
gallery's Gaussian-integral result into a reusable probabilistic object and exercises Mathlib's
integration-by-parts and even/odd-symmetry integral lemmas.

## Known Results

### What's Already Proven

- Parent `area-of-circle-oq-05-incomplete-01` — the Gaussian normalization `∫ e^{−x²/2} dx = √(2π)`
  (the `k = 0` moment, `E[X⁰] = 1`).
- Mathlib `integral_gaussian`, `MeasureTheory.integral_mul_deriv_eq_deriv_mul` (integration by
  parts), and `MeasureTheory.integral_comp_neg` / odd-function integral vanishing lemmas.

### What's Still Open

- The general even-moment formula `E[X^{2k}] = (2k−1)!!` and odd-moment vanishing (this problem).

### Our Goal

Prove, over the standard normal density, (1) `∫ x^{2k+1} φ(x) dx = 0` by odd symmetry, and (2)
`∫ x^{2k} φ(x) dx = (2k−1)!!` by the integration-by-parts recursion with base case the Gaussian
normalization. Express `(2k−1)!!` via `Nat.doubleFactorial` and induct on `k`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-05-incomplete-01 | Parent; Gaussian normalization (base case) | Gaussian integral |
| area-of-circle | Ancestor; πr² and related integral machinery | integration |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Integration-by-parts recursion + induction on k.
   - Why it might work: `E[X^{2k}] = (2k−1) E[X^{2k−2}]` follows from IBP with `u = x^{2k−1}`,
     `dv = x e^{−x²/2} dx`; induction with base `E[X⁰] = 1` gives `(2k−1)!!`. Mathlib has the IBP
     lemma and the base case.
   - Risk: the boundary terms at ±∞ vanish (Gaussian decay); justifying the improper-integral IBP
     and integrability of `x^{2k} e^{−x²/2}` needs Mathlib's `integrable`/decay lemmas.

2. **Approach B**: Moment generating function `M(t) = e^{t²/2}` and Taylor coefficients.
   - Why it might work: reading off `E[X^n]` from the MGF series `e^{t²/2} = Σ t^{2k}/(2^k k!)` gives
     `E[X^{2k}] = (2k)!/(2^k k!) = (2k−1)!!` directly.
   - Risk: requires formalizing the MGF and interchanging expectation with the power series, which
     is heavier than the direct recursion.

### Key Difficulties

- Integrability of `x^{n} e^{−x²/2}` over ℝ and vanishing boundary terms in the IBP step.
- Matching the recursion output to `Nat.doubleFactorial` / `(2k)!/(2^k k!)` cleanly.

### What Would a Proof Need?

- Key lemma 1: integrability `Integrable (fun x => x^n * exp(-x²/2))` for all `n` (Gaussian decay).
- Key lemma 2: the IBP recursion `E[X^{2k}] = (2k−1) E[X^{2k−2}]` and odd-symmetry vanishing.
- Technical requirements: `integral_gaussian`, IBP lemma, `Nat.doubleFactorial`, odd-function
  integral = 0.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib provides the Gaussian integral, integration-by-parts, and odd-function integral lemmas.
- The recursion is standard and the induction is elementary once integrability is established.
- Gaussian-integral results already exist in the gallery, so the base infrastructure is present.

**Estimated Effort**:
- Exploration: days
- If tractable: days to a week
- If hard: unknown (if improper-integral IBP boundary justification proves fiddly)

## References

### Papers
- Standard probability texts (Billingsley, *Probability and Measure*) — Gaussian moments and the
  double-factorial formula.

### Online Resources
- https://en.wikipedia.org/wiki/Normal_distribution#Moments — `E[X^{2k}] = (2k−1)!!`.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gaussian` — `integral_gaussian` and Gaussian integrability.
- `Mathlib.MeasureTheory.Integral.IntegrationByParts` — IBP for interval/improper integrals.
- `Mathlib.Combinatorics` / `Nat.doubleFactorial` — `(2k−1)!!`.

## Metadata

```yaml
tags:
  - analysis
  - gaussian-integral
  - normal-distribution
  - probability
  - integration
  - double-factorial
related_proofs:
  - area-of-circle-oq-05-incomplete-01
  - area-of-circle
difficulty: medium
source: proof-suggestion
created: 2026-07-02T02:47:20-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
