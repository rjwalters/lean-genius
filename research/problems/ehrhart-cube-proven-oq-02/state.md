# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — `crossEhrhart_is_poly` closed (PR #16734); `crossBall_card`
succ-d remains
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-07
**Iteration**: 2

## Current Focus
One sorry remains in `proofs/Proofs/EhrhartCrossPolytope.lean`:
- `crossBall_card` succ-d case — Finset slicing decomposition by last
  coordinate (≈100 lines, deferred to a future session).

## Active Approach
- For (1), use Mathlib's `descPochhammer ℚ k` (degree k, evaluates to
  `n.descFactorial k = k! · C(n,k)` at Nat n via
  `descPochhammer_eval_eq_descFactorial`). Construct
  `P = ∑ k ∈ range (d+1), C ((2:ℚ)^k · C(d,k) / k!) · descPochhammer ℚ k`.
  - natDegree bound via `Polynomial.natDegree_sum_le` + `descPochhammer_natDegree`.
  - Eval property via `Polynomial.eval_finset_sum` + `descPochhammer_eval_eq_descFactorial`
    + `Nat.descFactorial_eq_factorial_mul_choose`. The `k!` in the C-coefficient
    cancels against `descFactorial = k! · choose`, leaving `2^k · C(d,k) · C(n,k)`.

- For (2), the Finset slicing uses
  `crossBall (d+1) n` decomposition by last coordinate j ∈ Fin (2n+1):
  for j = n + δ (δ ∈ {-n,…,n}), the fiber is `crossBall d (n - |δ|)`.
  Pairing j ↔ 2n − j gives `card = crossBall_d_n + 2·∑_{m<n} crossBall_d_m`,
  which by IH and `crossEhrhart_succ_d` matches `crossEhrhart (d+1) n`.
  Implementation: `Finset.card_eq_sum_card_fiberwise` over the projection
  `x ↦ x ⟨d, ...⟩`, then split the fiber sum into the m=n case (one fiber)
  and the rest paired symmetrically.

## Attempt Count
- Total attempts: 2
- Approaches tried: descPochhammer-based polynomial construction (Session 1
  planned, Session 2 implemented and shipped via PR #16734)

## Blockers
- **Local Lean build**: Worktree's `proofs/.lake` symlink is a self-cycle; my
  Docker build attempt hung on `mathlib: cloning` for 14+ minutes without
  reaching the cache. Closing sorries without local verification is risky.
  PR-driven CI will validate, but iteration cost is high.

## Next Action
**Pause for CI verification of PR #16734** before tackling `crossBall_card`
succ-d. The Finset slicing decomposition is intricate (≈100 lines) and
should follow the sketch in knowledge.md Session 1: fiberwise count via
`Finset.card_eq_sum_card_fiberwise` over the last-coordinate projection,
plus a symmetric pairing j ↔ 2n − j.

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:249-255` — `crossEhrhart_is_poly` sorry
- `proofs/Proofs/EhrhartCrossPolytope.lean:267-283` — `crossBall_card` sorry
- Mathlib: `Mathlib.RingTheory.Polynomial.Pochhammer` (descPochhammer)
- Mathlib: `Nat.cast_choose_eq_descPochhammer_div` — alternate form of the
  evaluation identity
