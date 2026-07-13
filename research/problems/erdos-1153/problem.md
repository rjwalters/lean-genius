# Problem: Erdős #1153

## Statement

### Plain Language

For any subinterval $[a, b]$ of $[-1, 1]$ and any $n$ distinct interpolation
nodes in $[-1, 1]$, the maximum on $[a, b]$ of the Lebesgue function
$\lambda(x) = \sum_k |l_k(x)|$ (where $l_k$ are the Lagrange basis
polynomials) exceeds $(2/\pi - o(1)) \log n$. The constant $2/\pi$ is
sharp, achieved asymptotically by Chebyshev polynomial roots.

### Formal Statement

$$
\forall \varepsilon > 0,\ \forall -1 \leq a < b \leq 1,\
\exists N \in \mathbb{N},\ \forall n \geq N,\
\forall (x_k)_{k=1}^n \subset [-1,1] \text{ distinct},\
\exists x \in [a, b]:\
\lambda(x) \geq \left(\tfrac{2}{\pi} - \varepsilon\right) \log n.
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 6
erdosNumber: 1153
erdosUrl: https://erdosproblems.com/1153

tags:
  - erdos
  - analysis
  - polynomials
  - interpolation
  - approximation-theory
  - solved
```

**Significance**: 7/10
**Tractability**: 6/10
**Database status**: SOLVED (Erdős 1961, sharpening Bernstein 1931)

## Why This Matters

1. **Erdős Legacy** — Part of Paul Erdős's influential problem collection
   on approximation theory and polynomial interpolation.
2. **Fundamental barrier** — Demonstrates a universal logarithmic lower
   bound for the condition number of Lagrange interpolation, independent
   of node placement strategy.
3. **Chebyshev optimality** — The sharp constant $2/\pi$ is achieved by
   Chebyshev polynomial roots, providing a concrete optimal node family.
4. **Subinterval universality** — The growth cannot be avoided even on
   small subintervals; the phenomenon is locally intrinsic.

## Formalization Status

Already formalized in `proofs/Proofs/Erdos1153Problem.lean`:

- 4 definitions: `lagrangeBasis`, `lebesgueFunction`, `NodesInInterval`,
  `DistinctNodes`
- 6 theorems (Kronecker delta, nonnegativity, value at nodes, full-interval
  corollary)
- 1 axiom: `erdos_1153` — the asymptotic logarithmic lower bound
- 0 sorries

Gallery entry: `src/data/proofs/erdos-1153/` (status `axiomatized`,
badge `axiom`).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-1129` | Related Erdős problem on interpolation and Lebesgue constants |
| `erdos-1132` | Related Erdős problem on polynomial interpolation |

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

- Bernstein, S. (1931): "On the distribution of zeros of Lagrange
  interpolation polynomials" — original logarithmic lower bound.
- Erdős, P. (1961): "Problems and results on the theory of interpolation,
  II" [Er61c] — sharp $2/\pi$ constant.
- Vaughan [Va99, 2.44]: Survey of Erdős problems in analysis.

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
