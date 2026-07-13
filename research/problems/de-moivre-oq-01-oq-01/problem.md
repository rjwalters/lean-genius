# Problem: Binomial Expansion of cos(nθ) and the Chebyshev Polynomial Tₙ

**Slug**: de-moivre-oq-01-oq-01
**Created**: 2026-07-01T08:49:18-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\cos(n\theta) = \sum_{j=0}^{\lfloor n/2\rfloor} (-1)^j \binom{n}{2j} \cos^{\,n-2j}\theta \,\sin^{2j}\theta = T_n(\cos\theta),
$$

where $T_n$ is the degree-$n$ Chebyshev polynomial of the first kind.

### Plain Language

Expanding $(\cos\theta + i\sin\theta)^n$ by the binomial theorem and taking real parts gives $\cos(n\theta)$ as an alternating sum of binomial coefficients times powers of $\cos\theta$ and $\sin\theta$. After substituting $\sin^2\theta = 1-\cos^2\theta$, the result is a polynomial in $\cos\theta$ — exactly the Chebyshev polynomial $T_n$.

### Why This Matters

This is the concrete payoff of De Moivre's theorem: it produces the multiple-angle formulas and reveals $T_n$ as the polynomial encoding $\cos(n\theta)$. Chebyshev polynomials are central to approximation theory, numerical analysis, and orthogonal polynomial theory; connecting the elementary De Moivre expansion to `Polynomial.Chebyshev.T` closes a satisfying loop in the gallery.

## Known Results

### What's Already Proven

- De Moivre's theorem `(cos θ + i sin θ)^n = cos nθ + i sin nθ` — parent entry `de-moivre-oq-01`.
- Mathlib defines `Polynomial.Chebyshev.T` and proves `Polynomial.Chebyshev.T_complex_cos` / `T_real_cos`: `(T n).eval (cos θ) = cos (n θ)`.
- Binomial theorem and `Complex.exp`/`Complex.cos` API.

### What's Still Open

- A formal derivation of the explicit alternating-binomial-sum form of `cos(nθ)` from De Moivre (taking real parts).
- Explicitly identifying that sum with `(Polynomial.Chebyshev.T ℝ n).eval (cos θ)`.

### Our Goal

Formalize the alternating binomial expansion of `cos(nθ)` by taking real parts of the binomial expansion of `(cos θ + i sin θ)^n`, then prove it equals `T_n(cos θ)` by connecting to Mathlib's `Chebyshev.T_real_cos`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-01 | Parent: multiple-angle formulas | De Moivre, complex powers |
| de-moivre | Base theorem | complex exponentials |
| binomial-theorem | Expansion of the n-th power | binomial coefficients |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Expand `(cos θ + i·sin θ)^n` via `Complex.add_pow` / binomial theorem, take `Complex.re`, and collect even-index terms (which carry `i^{2j} = (-1)^j`).
   - Why it might work: purely algebraic; real part isolates the cosine sum.
   - Risk: reindexing to even `j` and tracking powers of `i`.

2. **Approach B**: Prove the sum equals `T_n(cos θ)` by invoking `Chebyshev.T_real_cos` (`cos nθ = T_n(cos θ)`) and separately showing the binomial sum equals `cos nθ`.
   - Why it might work: routes through the existing Mathlib Chebyshev bridge.
   - Risk: still need the real-part extraction for the explicit sum form.

### Key Difficulties

- Isolating the real part as a sum over even indices with the correct `(-1)^j` sign.
- Substituting `sin²θ = 1 - cos²θ` to reach a genuine polynomial in `cos θ`.

### What Would a Proof Need?

- Key lemma 1: real part of `(cos θ + i sin θ)^n` equals the alternating even-index binomial sum.
- Key lemma 2: `cos(nθ) = T_n(cos θ)` (Mathlib `Chebyshev.T_real_cos`).
- Technical requirements: `Complex.add_pow`, `Finset.sum` even/odd split, powers of `Complex.I`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Chebyshev↔cosine bridge already exists in Mathlib (`T_real_cos`).
- The binomial real-part extraction is a finite, mechanical computation.
- Comparable multiple-angle formalizations are standard.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 2–4 days
- If hard: n/a

## References

### Papers
- Standard: Rivlin, *Chebyshev Polynomials* — trigonometric definition.

### Online Resources
- https://en.wikipedia.org/wiki/Chebyshev_polynomials#Trigonometric_definition — the identity.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev` — `Polynomial.Chebyshev.T_real_cos`, `T_complex_cos`.

## Metadata

```yaml
tags:
  - trigonometry
  - polynomials
  - complex-analysis
related_proofs:
  - de-moivre-oq-01
  - binomial-theorem
difficulty: low
source: gallery-gap
created: 2026-07-01T08:49:18-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
