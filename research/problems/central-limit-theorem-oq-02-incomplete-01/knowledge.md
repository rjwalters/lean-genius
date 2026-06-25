# Knowledge Base: central-limit-theorem-oq-02-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2 (2026-06-25) — COMPLETED

Proved the symmetrised **Bienaymé identity** in `CentralLimitTheoremOQ02Incomplete01.lean`:

    Var[∑ᵢ Xᵢ] = ∑ᵢ Var[Xᵢ] + 2·∑_{i<j} Cov[Xᵢ, Xⱼ]

refining Mathlib's `variance_sum'` (which gives only the unsymmetrised double sum
∑ᵢ∑ⱼ Cov). Four theorems, **0 axioms, 0 sorries** (only propext/Classical.choice/Quot.sound).

### What worked
- `Finset.diag_union_offDiag` to split s×s; `covariance_self` for the diagonal → Var.
- Off-diagonal symmetrisation via `Finset.sum_nbij'` with the `Prod.swap` involution
  and `covariance_comm`: ∑_offDiag = 2·∑_{i<j}.
- `covariance_comm` needs **explicit arguments** `covariance_comm (X a) (X b)` — the
  bare term left the random-variable metavars unresolved (type mismatch).

### Specialisations
- `variance_sum_of_pairwise_uncorrelated`: correction vanishes → additivity (√n CLT).
- `variance_partialSum_eq`: Var[Sₙ] over `range n`; its n→∞ limit is σ²∞.

### Follow-ups
- Stationary summable-autocovariance ⇒ Var[Sₙ]/n → σ²∞.
- Symmetrisation for an arbitrary fixed pairing (drop the linear order).
