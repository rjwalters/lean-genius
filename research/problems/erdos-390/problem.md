# Problem: Erdős #390

## Statement

### Plain Language
Let $f(n)$ be the minimal $m$ such that $n! = a_1 \cdot a_2 \cdots a_k$ with
$n < a_1 < a_2 < \cdots < a_k = m$. Is there (and if so, what is) a constant $c$
such that $f(n) - 2n \sim c \cdot n / \log n$?

Erdős, Guy, and Selfridge [EGS82] showed that $f(n) - 2n \asymp n/\log n$
(i.e., the excess has order of magnitude $n/\log n$, but a sharp asymptotic
with a single constant $c$ is unknown).

### Formal Statement

Let $f(n)$ be the minimal $m$ such that there exist integers $a_1 < a_2 < \cdots < a_k = m$
with $a_i > n$ and $\prod a_i = n!$. Does
$$\lim_{n \to \infty} (f(n) - 2n) \cdot \frac{\log n}{n}$$
exist for some positive constant $c$?

## Classification

```yaml
tier: C
significance: 6
tractability: 4
erdosNumber: 390
erdosUrl: https://erdosproblems.com/390
status: axiomatized

tags:
  - erdos
  - number-theory
  - factorials
  - asymptotics
  - open
```

**Significance**: 6/10 (deep open question at the intersection of factorial
arithmetic, prime distribution, and integer optimization)
**Tractability**: 4/10 (resolution requires improving on the 1982 Erdős–Guy–Selfridge
bound)

## Why This Matters

1. **Asymptotic precision in factorial factorization**: A positive answer would
   reveal the leading-order constant in the optimal large-factor decomposition
   of $n!$, sharpening the 1982 EGS qualitative bound to a quantitative one.
2. **Prime distribution connection**: The $n/\log n$ scale is exactly the prime
   counting function's growth rate. Primes $p \in (n, 2n]$ contribute exactly
   once to $(2n)!/n!$ but may need redistribution via composite factors, so the
   constant $c$ (if it exists) encodes how the Prime Number Theorem mediates
   factorial restructuring.
3. **The number 239**: The EGS title refers to the curiosity that $239$ is the
   smallest prime $p$ such that $p(p+1)/2$ is not a product of primes $\leq p$.
   The constant $c$ would systematize this kind of arithmetic anomaly.
4. **Erdős legacy**: One of the cleaner open problems in factorial combinatorics
   from the Erdős collection — easy to state, easy to compute small cases,
   yet the asymptotic constant has resisted determination for over 40 years.

## Current Lean Formalization

**Status**: `axiomatized` (gallery), `MATURE-AXIOMATIZED` (research)
**Source**: `proofs/Proofs/Erdos390Problem.lean` (538 lines)
**Sorries**: 0
**Axioms**: 1 (`factorizationMax_asymptotic`, the EGS two-sided bound)

Verified content:
- `ValidFactorization n` structure (sorted factors $> n$ with product $= n!$)
- Exact values $f(3) = 6$, $f(4) = 24$, $f(5) = 12$, $f(6) = 10$, $f(7) = 20$, $f(8) = 16$
  with tight upper- and lower-bound proofs (case-analysis on factorization length;
  upper bounds are computational via `native_decide`)
- Structural properties $f(n) > n$ and $f(n) \leq n!$ for $n \geq 3$
- The open conjecture is stated as `ErdosProblem390 : Prop` using `Filter.Tendsto`

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| (none yet — this is a leaf in the factorial-asymptotics cluster) | — |

## Related Problems

The Erdős database flags the following as related:

- [Problem #2000](https://www.erdosproblems.com/2000) — Erdős–Graham related
- [Problem #83](https://www.erdosproblems.com/83) — factorial divisibility
- [Problem #888](https://www.erdosproblems.com/888) — multiplicative number theory
- [Problem #1998](https://www.erdosproblems.com/1998) — combinatorial number theory
- [Problem #389](https://www.erdosproblems.com/389) — sibling factorial problem
- [Problem #391](https://www.erdosproblems.com/391) — sibling factorial problem
- [Problem #2](https://www.erdosproblems.com/2) — base case
- [Problem #39](https://www.erdosproblems.com/39) — analytic NT
- [Problem #1](https://www.erdosproblems.com/1) — root index

## References

- **[EGS82]** Erdős, P., Guy, R. K., and Selfridge, J. L., "Another property of 239
  and some related questions", Congr. Numer. **35** (1982), 243–257. The primary
  reference establishing $f(n) - 2n \asymp n/\log n$ for $n \geq 10$.
- **[ErGr80]** Erdős, P. and Graham, R. L., *Old and New Problems and Results in
  Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique 28,
  L'Enseignement Mathématique, Geneva, 1980. Background discussion.

## OEIS Sequences

- [A193429](https://oeis.org/A193429) — main sequence $f(n)$ for $n \geq 1$
- [C124171](https://oeis.org/C124171) — auxiliary cross-reference
- [B884451](https://oeis.org/B884451) — auxiliary cross-reference
- [C042214](https://oeis.org/C042214) — auxiliary cross-reference

## Computed Values (from formalization)

The Lean formalization verifies:

| $n$ | $n!$    | $f(n)$ | $f(n) - 2n$ |
|----:|--------:|-------:|------------:|
|  3  |       6 |     6  |          0  |
|  4  |      24 |    24  |         16  |
|  5  |     120 |    12  |          2  |
|  6  |     720 |    10  |         -2  |
|  7  |    5040 |    20  |          6  |
|  8  |   40320 |    16  |          0  |

The non-monotonic behavior of $f(n) - 2n$ (especially $f(6) - 12 = -2$, where
$f(6) = 10 < 12$ because $6! = 720 = 8 \cdot 9 \cdot 10$ avoids the $(6, 12]$
window) illustrates why the asymptotic question is delicate: small-$n$ values
do not extrapolate cleanly to the EGS regime $n \geq 10$.
