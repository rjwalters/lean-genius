# Problem: Erdős #1141 — Coprime-Square Subtraction Primes

## Statement

### Plain Language

Are there infinitely many natural numbers $n$ such that $n - k^2$ is prime for every $k$ satisfying $\gcd(n, k) = 1$ and $k^2 < n$?

### Formal Statement

$$
\#\Bigl\{ n \in \mathbb{N} \;\Bigm|\; \forall k \in \mathbb{N},\; \gcd(n, k) = 1 \;\wedge\; k^2 < n \;\Longrightarrow\; (n - k^2) \text{ is prime} \Bigr\} \stackrel{?}{=} \infty
$$

### Status (2026)

**SOLVED**. Answer: **NO** — only finitely many such $n$ exist.

Proved by Alexeev, Putterman, Sawhney, Sellke, and Valiant (2026, arXiv:2604.06609). More generally, for each fixed $a \geq 1$, the set $\{n : (n - ak^2) \text{ prime for all coprime } k \text{ with } ak^2 < n\}$ is finite. The proof is a short deduction from Pollack's 2017 theorem on small prime quadratic residues. The bound is ineffective (Siegel's theorem); computationally, $n = 1722$ appears to be the largest good value for $a = 1$ (verified to $10^{10}$).

## Classification

```yaml
tier: A
significance: 7
tractability: 6
erdosNumber: 1141
erdosUrl: https://erdosproblems.com/1141
erdosProblemStatus: solved
solverYear: 2026
solverReference: arXiv:2604.06609

tags:
  - erdos
  - number-theory
  - primes
  - computational
  - solved
```

**Significance**: 7/10 — A clean number-theoretic question on the intersection of additive and multiplicative structure (primes, coprimality, squares); the SOLVED 2026 status (via Pollack's theorem) connects it to modern small-prime analytic number theory.

**Tractability** (for Lean formalization of the slug): 6/10 — The decidable predicate, computational verification of 41 known good values, structural corollaries, and complete classification up to $n = 100$ are routine; the finiteness axiom encoding APSSV 2026 will become provable only once Pollack's theorem reaches Mathlib.

## Why This Matters

1. **Erdős Legacy** — Part of Paul Erdős's influential problem collection; cited in Erdős–Graham 1980 and Erdős's 1976 Manitoba lectures.
2. **Highly composite structure** — All known good values except $n = 3$ are even, and many are highly composite ($24, 30, 60, 90, 180, 252, 360, 570$). The pattern has a natural explanation: highly composite $n$ have small $\varphi(n)/n$, meaning fewer coprime $k$ values and hence fewer simultaneous primality conditions.
3. **Recently solved (2026)** — Modern resolution via Pollack's theorem on small prime quadratic residues demonstrates how recent analytic number theory results can close decades-old Erdős problems.
4. **Decidability and computational verification** — The bounded-quantifier formulation makes the predicate decidable, enabling `decide`/`native_decide` tactics to verify or refute the property for specific $n$. A clean exemplar for decidable number-theoretic predicates in Lean.

## Related Gallery Proofs

| Slug | Relationship | Description |
|------|--------------|-------------|
| [erdos-1140](https://erdosproblems.com/1140) | structural-sibling | Same question with $2x^2$ instead of $k^2$; Epure–Gica (2022) disproved infinitude (resolved precedent for the analogous question). |
| [erdos-1142](https://erdosproblems.com/1142) | structural-sibling | Replaces $k^2$ with $2^k$ ($n - 2^k$ prime for all $1 < 2^k < n$); also unresolved with even sparser known values. |
| [erdos-1059](https://erdosproblems.com/1059) | thematic | Asks about primes $p$ with $p - k!$ composite for all $k! < p$; dual flavor (universal compositeness vs universal primeness). |
| [erdos-680](https://erdosproblems.com/680) | thematic | Least prime factor near $n$ exceeding $k^2 + 1$; same quadratic-prime interplay. |
| [erdos-17](https://erdosproblems.com/17) | thematic | Cluster primes: every even $n \leq p - 3$ a difference of two primes $\leq p$; universal-primeness flavor. |
| [erdos-203](https://erdosproblems.com/203) | methodological | Covering systems for prime avoidance; potential proof tool for finiteness of good-value sequences. |

## Related Problems (Erdős cross-links)

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- **P. Erdős** (1976), "Problems in number theory and combinatorics", *Proceedings of the Sixth Manitoba Conference on Numerical Mathematics*, pp. 35–58. Original source for the family.
- **P. Erdős and R. L. Graham** (1980), *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique, vol. 28, Université de Genève. Canonical reference.
- **ChatGPT-Tang** (2023), density bound $\#\{n \leq N : \text{IsGood}(n)\} = O(N^{1/2 + o(1)})$ for OEIS A214583, communicated via erdosproblems.com comment.
- **A. Epure and A. Gica** (2022), "On a conjecture of Erdős concerning primes of the form $n - 2x^2$", *Journal of Number Theory*. Disproves infinitude for the $a = 2$ variant (resolved precedent).
- **D. Alexeev, M. Putterman, M. Sawhney, A. Sellke, P. Valiant** (2026), arXiv:2604.06609. Solves the problem: for every fixed $a \geq 1$, only finitely many $n$ have $n - ak^2$ prime for all coprime $k$ with $ak^2 < n$. Proof deduces from Pollack (2017).
- **P. Pollack** (2017), small-prime-quadratic-residues theorem. Provides $a \pmod{q}$ small-prime-coverage that powers the APSSV deduction. Not yet in Mathlib.

## OEIS Sequences

- [A214583](https://oeis.org/A214583) — the 41 known good values: $3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 38, 42, 48, 54, 60, 62, 68, 72, 80, 84, 90, 98, 108, 110, 132, 138, 140, 150, 180, 182, 198, 252, 318, 360, 398, 468, 570, 572, 930, 1722$. No further terms below $10^{10}$.
