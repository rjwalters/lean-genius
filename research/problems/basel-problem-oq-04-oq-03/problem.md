# Problem: Formalize Pr[gcd(m,n)=1] = 6/π² via Mathlib Measure Theory

**Slug**: basel-problem-oq-04-oq-03
**Created**: 2026-04-26T08:14:43+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\lim_{N \to \infty} \frac{|\{(m,n) : 1 \le m,n \le N,\ \gcd(m,n) = 1\}|}{N^2} = \frac{6}{\pi^2} = \frac{1}{\zeta(2)}
$$

Equivalently, if $(m, n)$ are chosen uniformly at random from $\{1, \ldots, N\}^2$,
then $\Pr[\gcd(m, n) = 1] \to 6/\pi^2$ as $N \to \infty$.

### Plain Language

Two integers chosen at random are coprime with probability $6/\pi^2 \approx 0.608$.
This result connects combinatorics, number theory, and probability:
- $\Pr[\gcd(m,n)=1] = \prod_p (1 - 1/p^2) = 1/\zeta(2) = 6/\pi^2$

The proof uses inclusion-exclusion over primes and the Euler product for ζ(2).

### Why This Matters

- **Classic result**: One of the most elegant connections in mathematics
- **Multiple proof paths**: Euler product, Möbius function, or natural density
- **Mathlib tractability**: `Nat.Coprime`, `ArithmeticFunction.pmul`, Euler products
- **Gallery connection**: Complements `basel-problem` (ζ(2) = π²/6) probabilistically

## Known Results

### What's Already Proven

- `basel-problem` (gallery) — ζ(2) = π²/6
- Mathlib: `Nat.Coprime`, `Nat.gcd`, Möbius in `NumberTheory.ArithmeticFunction`

### What's Still Open

- Formal density statement: `Filter.Tendsto (fun N => count_coprime N / N²) atTop (nhds (6/π²))`
- Proof connecting density limit to ζ(2) = π²/6

### Our Goal

Formalize the probabilistic statement as a `Filter.Tendsto` result:
```lean
theorem coprime_density :
    Filter.Tendsto (fun N : ℕ => (Finset.card {p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N |
      Nat.Coprime p.1 p.2} : ℝ) / N^2) Filter.atTop (nhds (6 / Real.pi^2)) := by ...
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem | ζ(2) = π²/6 (core ingredient) | Fourier series |
| basel-problem-oq-04 | Euler product formula | Dirichlet series |
| infinitude-of-primes | Prime enumeration | Euclid |

## Initial Thoughts

### Potential Approaches

1. **Möbius function approach**: Use Möbius inversion and φ(n)/n → 1/ζ(2).
   - Why it might work: Mathlib has Möbius in `ArithmeticFunction`
   - Risk: More steps, Cesàro averaging needed

2. **Euler product approach**: Product ∏_p (1 - 1/p²) = 1/ζ(2) directly.
   - Why it might work: Gallery has ζ(2) = π²/6
   - Risk: Convergence of density to product needs analysis

### Key Difficulties

- `tendsto (count_coprime N / N²) atTop (nhds (6/π²))`
- Connecting density limit to the Euler product

### What Would a Proof Need?

- Key lemma 1: Möbius identity `∑ d | n, μ(d) = [n = 1]` (in Mathlib)
- Key lemma 2: Density of coprime pairs via Cesàro summation
- Core result: gallery `basel-problem` ζ(2) = π²/6

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical result, Mathlib has the building blocks
- Main challenge: density limit convergence and connection to ζ(2) = π²/6

**Estimated Effort**:
- Exploration: 1-2 days (Mathlib Möbius and density API survey)
- If tractable: 1-2 weeks

## References

- Cesàro (1885) — first explicit statement
- Hardy & Wright — *Theory of Numbers*, Chapter XVIII
- `Mathlib.NumberTheory.ArithmeticFunction` — Möbius function

## Metadata

```yaml
tags:
  - number-theory
  - probability
  - zeta-function
  - measure-theory
  - coprime-density
  - seeker-selected
related_proofs:
  - basel-problem
  - basel-problem-oq-04
  - infinitude-of-primes
difficulty: medium
source: gallery-gap
created: 2026-04-26T08:14:43+02:00
```

**Significance**: 8/10
**Tractability**: 6/10
