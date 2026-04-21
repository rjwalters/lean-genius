# Problem: Variance of Gambler's Ruin Stopping Time

**Slug**: fair-games-theorem-oq-02-oq-03
**Created**: 2026-04-21T20:38:02+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $(S_n)_{n \geq 0}$ be a simple symmetric random walk starting at $S_0 = k \in \{1, \ldots, N-1\}$ with absorbing barriers at $0$ and $N$. Let $\tau = \inf\{n : S_n \in \{0, N\}\}$ be the ruin time. Formalize:

$$\text{Var}(\tau) = \frac{k(N-k)(N^2 - k(N-k))}{6} \cdot \frac{1}{?}$$

or the precise classical variance formula for $\tau$.

### Plain Language

The expected ruin time is $E[\tau] = k(N-k)$, as proved in `fair-games-theorem-oq-02`. The **variance** $\text{Var}(\tau) = E[\tau^2] - E[\tau]^2$ is harder: it involves the second moment $E[\tau^2]$, which requires a degree-4 martingale or optional stopping applied to a polynomial of degree 4.

### Why This Matters

The variance formula completes the second-moment analysis of the Gambler's Ruin, a fundamental result in probability theory. It is needed for concentration inequalities and CLT-type results for stopped random walks.

## Known Results

### What's Already Proven

- `fair-games-theorem-oq-02`: $E[\tau] = k(N-k)$ and ruin probability $P(\text{ruin at } 0) = 1 - k/N$. (verified, 0 sorries)
- `fair-games-theorem-oq-02-oq-01`: Optional Stopping Theorem in Lean.
- Standard martingale: $S_n^2 - n$ is a martingale for simple random walk.

### What's Still Open

- $\text{Var}(\tau)$ formalization.
- The degree-4 process $S_n^4 - 6nS_n^2 + 3n^2 + 2n$ (or similar) needed for $E[\tau^2]$.

### Our Goal

Compute $E[\tau^2]$ using the quartic martingale and derive $\text{Var}(\tau)$ via the identity $\text{Var}(\tau) = E[\tau^2] - E[\tau]^2$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fair-games-theorem-oq-02` | Expected ruin time | Martingale OST |
| `fair-games-theorem-oq-02-oq-01` | Optional Stopping | Doob's OST |
| `fair-games-theorem` | Martingale basics | `MartingaleProcess` |

## Initial Thoughts

### Potential Approaches

1. **Quartic martingale**: Define $M_n = S_n^4 - 6n S_n^2 + 3n^2 + 2n$ (or the correct degree-4 polynomial) and apply OST to get $E[\tau^2]$.
   - Why it might work: Standard technique in stochastic calculus.
   - Risk: Verifying the martingale property requires polynomial arithmetic in Lean.

2. **Generating function approach**: Use $E[z^\tau]$ and differentiate twice.
   - Why it might work: The generating function for simple RW ruin times is known.
   - Risk: Complex analysis in Lean for formal power series.

### Key Difficulties

- Finding the correct quartic martingale expression.
- Verifying optional stopping applies (bounded increment, bounded $\tau$ or bounded $M_n$).

### What Would a Proof Need?

- The quartic polynomial identity showing $M_n = S_n^4 - 6nS_n^2 + 3n^2 + 2n$ is a martingale.
- Optional stopping applied at $\tau$: $E[M_\tau] = M_0 = k^4$.
- Algebra to extract $E[\tau^2]$ from the OST equation.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The expected value case (using $S_n^2 - n$) was already done in the parent proof.
- The quartic generalization follows the same pattern with more algebra.
- Mathlib has the martingale optional stopping machinery from `fair-games-theorem-oq-02-oq-01`.

## References

### Papers
- Feller, W. *An Introduction to Probability Theory and Its Applications*, Vol. 1, Ch. XIV.

### Mathlib
- `MeasureTheory.StoppedValue` — stopped processes
- `MeasureTheory.Martingale` — martingale definition
- `MeasureTheory.OptionalStopping` — OST

## Metadata

```yaml
tags:
  - probability
  - martingales
  - stochastic-processes
  - gambler-ruin
related_proofs:
  - fair-games-theorem-oq-02
  - fair-games-theorem-oq-02-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-21T20:38:02+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
