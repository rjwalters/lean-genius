# Problem: Erdős #1149 — Coprimality of n and ⌊n^α⌋

## Statement

### Plain Language
For non-integer α > 0, what is the natural density of integers n such that gcd(n, ⌊n^α⌋) = 1?

**Solved (Bergelson–Richter 2017)**: the density is exactly 6/π² ≈ 0.608, the same as the classical "probability that two random integers are coprime."

### Formal Statement
$$
\lim_{N \to \infty} \frac{|\{n \leq N : \gcd(n, \lfloor n^\alpha \rfloor) = 1\}|}{N} = \frac{6}{\pi^2}, \quad \alpha > 0,\ \alpha \notin \mathbb{Z}.
$$

The integer case is degenerate: for α = k ∈ ℤ_{≥1}, gcd(n, n^k) = n, so only n = 1 is coprime (density 0).

## Classification

```yaml
tier: B
significance: 7
tractability: 6
erdosNumber: 1149
erdosUrl: https://erdosproblems.com/1149

tags:
  - erdos
  - number-theory
  - coprimality
  - asymptotic-density
  - floor-function
  - ergodic-theory
  - zeta-function
```

**Significance**: 7/10
**Tractability**: 6/10 (main theorem axiomatized; supporting Möbius infrastructure proved)

## Why This Matters

1. **Erdős Legacy** — Part of Paul Erdős's influential problem collection.
2. **Independence phenomenon** — n and ⌊n^α⌋ are deterministically related, yet their coprimality density matches that of two uniformly random integers; the non-integer hypothesis "destroys" arithmetic correlations.
3. **Connection to ζ(2)** — The density 6/π² = 1/ζ(2) = ∏_p(1 − 1/p²) ties the result to the Riemann zeta function and the Euler product.
4. **Gateway to multiplicative-along-polynomial-sequences** — The Bergelson–Richter proof uses ergodic theory and multiplicative function theory along polynomial sequences, a deep technique with broader applications.

## Formalization Status

- `Proofs/Erdos1149Problem.lean` (320 lines, 17 theorems, 5 definitions, **0 sorries, 2 axioms**)
- `Proofs/Erdos1149Aristotle.lean` (106 lines, 14 theorems, **0 sorries, 0 axioms**)

The 2 axioms in the main file:
- `bergelson_richter` — main theorem, deep ergodic theory; unlikely Mathlib-provable.
- `random_coprime_density` — classical Cesàro result; **infrastructure is in place** (`moebius_sum_divisors_eq`, `card_multiples`, `pairs_with_common_factor`) plus Mathlib's `hasSum_zeta_two`. Remaining gap is the Möbius–Tannery asymptotic interchange.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| euler-totient | Same coprimality predicate (φ counts coprimes). |
| infinitude-primes | Prime density underlies any Euler-product analysis. |
| prime-number-theorem | Sieve / counting techniques for coprimality density. |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- Bergelson, Richter (2017): *Multiplicative richness of additively large sets in Z^d*. Journal d'Analyse Mathématique.
- Erdős (1969 / 1983): *Some problems on number theory*, Marseille.
- Euler (1748): Euler product formula ζ(2) = π²/6 and 6/π² = ∏_p(1 − 1/p²).
- Cesàro (1881) / Sylvester: classical coprime-pair density 6/π².

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
