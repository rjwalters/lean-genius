# Problem: Biased Gambler's Ruin — Ruin Probability for p ≠ 1/2

**Slug**: fair-games-theorem-oq-02-oq-04
**Created**: 2026-04-21T20:38:04+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $(S_n)_{n \geq 0}$ be a biased random walk with $P(\text{step} = +1) = p$ and $P(\text{step} = -1) = q = 1-p$, starting at $S_0 = k$, with absorbing barriers at $0$ and $N$. For $p \neq 1/2$ (i.e., $p \neq q$), the ruin probability is:

$$P(\text{reach } 0 \text{ before } N \mid S_0 = k) = \frac{(q/p)^k - (q/p)^N}{1 - (q/p)^N}$$

Formalize this formula in Lean 4 as a theorem.

### Plain Language

The fair (unbiased) case $p = 1/2$ gives ruin probability $(N-k)/N$, proven in `fair-games-theorem-oq-02`. For $p \neq 1/2$ (e.g., a casino game where the house has an edge), the formula changes to an exponential expression in $q/p$. This is the classical biased random walk absorption formula.

### Why This Matters

The biased case is the practically important one: real casino games have $p < 1/2$. The formula shows exponential growth in the disadvantage — starting with $k$ chips against a house with $N-k$ chips, your ruin probability grows rapidly as $p$ decreases below $1/2$.

## Known Results

### What's Already Proven

- `fair-games-theorem-oq-02`: Unbiased case $p = 1/2$: ruin probability $= 1 - k/N$. (verified)
- The biased case uses the geometric sequence martingale $(q/p)^{S_n}$ instead of $S_n$.

### What's Still Open

- Formalization of the biased ruin probability.
- The expected ruin time for $p \neq 1/2$.

### Our Goal

Prove the biased ruin probability formula using the geometric martingale $(q/p)^{S_n}$ and optional stopping.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fair-games-theorem-oq-02` | Unbiased ruin probability | Linear martingale + OST |
| `fair-games-theorem-oq-02-oq-01` | Optional Stopping | Doob's OST |
| `fair-games-theorem` | Martingale basics | `MartingaleProcess` |

## Initial Thoughts

### Potential Approaches

1. **Geometric martingale**: Show $(q/p)^{S_n}$ is a martingale for biased walk, apply OST at $\tau$.
   - Why it might work: This is the textbook approach; all steps have Lean analogues.
   - Risk: Need to handle the case $p = 0$ or $p = 1$ separately (degenerate walk).

2. **Difference equation**: The ruin probability $u(k) = P(\text{ruin at 0} \mid S_0 = k)$ satisfies $u(k) = p \cdot u(k+1) + q \cdot u(k-1)$ with $u(0) = 1$, $u(N) = 0$. Solve this recurrence.
   - Why it might work: The recurrence is linear with constant coefficients; explicit solution is $(q/p)^k$.

### Key Difficulties

- The $(q/p)^{S_n}$ expression requires real-valued exponentiation or working in $\mathbb{R}$.
- Need OST hypotheses: $E[|\tau|] < \infty$ or bounded martingale for the geometric process.

### What Would a Proof Need?

- Lemma: $(q/p)^{S_n}$ is a martingale for biased walk.
- OST applied at ruin time $\tau$.
- Algebra: solve $(q/p)^k = P \cdot (q/p)^0 + (1-P) \cdot (q/p)^N$ for $P$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Closely analogous to the unbiased case (just swap the linear martingale for the geometric one).
- The key algebraic manipulation is straightforward.
- Mathlib's `NNReal.rpow` or `Real.rpow` handles the exponential.

## References

### Papers
- Feller, W. *An Introduction to Probability Theory and Its Applications*, Vol. 1, §XIV.2.

### Mathlib
- `Real.rpow` — real exponentiation
- `MeasureTheory.Martingale` — martingale definition
- `MeasureTheory.OptionalStopping` — OST

## Metadata

```yaml
tags:
  - probability
  - markov-chains
  - gambler-ruin
  - biased-random-walk
related_proofs:
  - fair-games-theorem-oq-02
  - fair-games-theorem-oq-02-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-21T20:38:04+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
