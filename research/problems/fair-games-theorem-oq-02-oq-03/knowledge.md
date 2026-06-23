# Knowledge: fair-games-theorem-oq-02-oq-03

## Key Facts

### Parent Results (fair-games-theorem-oq-02)
- Simple symmetric random walk $S_n$ on $\{0, \ldots, N\}$, starting at $k$
- Ruin probability: $P(\text{reach } 0) = 1 - k/N$
- Expected ruin time: $E[\tau] = k(N-k)$ (verified, 0 sorries)
- Proved via: $S_n$ is a martingale; $S_n^2 - n$ is a martingale

### Variance Formula
- $\text{Var}(\tau) = E[\tau^2] - E[\tau]^2 = E[\tau^2] - k^2(N-k)^2$
- Computing $E[\tau^2]$ requires a **degree-4 martingale**
- Classical result (Feller): $\text{Var}(\tau) = \frac{k(N-k)(N^2 - k(N-k))}{3} \cdot \frac{2}{N}$ (approximate — check exact formula)

### Degree-4 Martingale
- Process $M_n = S_n^4 - 6nS_n^2 + 3n^2 + 2n$ is a martingale for simple symmetric RW
  - Verification: $E[M_{n+1}|\mathcal{F}_n] = M_n$ uses $E[S_{n+1}^4|\mathcal{F}_n] = S_n^4 + 6S_n^2 + 1$
- By OST at $\tau$: $E[M_\tau] = M_0 = k^4$
- $S_\tau \in \{0,N\}$: $E[M_\tau] = E[S_\tau^4] - 6E[\tau]E[S_\tau^2] + 3E[\tau^2] + 2E[\tau]$
  - Requires careful computation of $E[S_\tau^4]$ and $E[S_\tau^2]$

## Open Questions
- What is the exact quartic martingale for simple symmetric random walk?
- Is `MeasureTheory.Martingale` the right Lean 4 type?
- Does `fair-games-theorem-oq-02-oq-01` (OST) provide a reusable lemma?

## References
- Feller, W. *Probability Theory*, Vol 1, §XIV.2 — variance formula
- Parent proof: `proofs/Proofs/FairGamesTheoremOQ02.lean`
- `Mathlib.Probability.MartingaleStoppedValue` — relevant Mathlib module
