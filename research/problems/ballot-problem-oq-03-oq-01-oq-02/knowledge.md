# Knowledge Base: ballot-problem-oq-03-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The hook-length formula $f^\lambda = n! / \prod_{u \in \lambda} h(u)$ counts SYT of shape λ.
The LGV approach: encode the Young diagram as a lattice path problem, apply `lgv_lemma_rxr`
from `BallotProblemOQ03OQ02.lean`, then factor the resulting determinant.

Key infrastructure already available:
- `lgvDet` (2×2) and `lgv_lemma_rxr` (n×n) — BallotProblemOQ03.lean + BallotProblemOQ03OQ02.lean
- `hook_length_formula_two_row` (numerical, 2-row case) — BallotProblemOQ03OQ03.lean

---

## Insights

- The 2-row case $C_m \cdot (m+1)! \cdot m! = (2m)!$ is already proved numerically.
  A structural proof using LGV would generalize: for λ = (m, m), the 2×2 LGV matrix
  has entries C(2m, m) and C(2m, m±1), and the determinant equals $C_m \cdot (m+1)! \cdot m!$.
- The n×n LGV lemma (BallotProblemOQ03OQ02.lean) uses `lgv_universality` — check its
  type signature before designing the hook-length encoding.
- For rectangular shape λ = (m^r): sources (0, r-i) for i=1..r, targets (m+r-i, 0).
  The LGV determinant = $\prod_{1≤i<j≤r} (λᵢ - i - λⱼ + j) / \prod ...$

---

## Dead Ends

[None yet — workspace initialized by Seeker 2026-04-21]
