# Research State: ehrhart-cube-proven-oq-02

## Current State
**Phase**: ACT — known proof path identified for `crossEhrhart_is_poly`
**Path**: incremental sorry closure
**Since**: 2026-05-07
**Last Updated**: 2026-05-07
**Iteration**: 1

## Current Focus
Two sorries remain in `proofs/Proofs/EhrhartCrossPolytope.lean`:
1. `crossEhrhart_is_poly` (line 255) — produce a `Polynomial ℚ` of degree ≤ d
   that evaluates to `crossEhrhart d n` at every Nat n.
2. `crossBall_card` succ-d case (line 283) — Finset slicing decomposition.

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
- Total attempts: 1 (this session)
- Approaches tried: descPochhammer-based polynomial construction (planned)

## Blockers
- **Local Lean build**: Worktree's `proofs/.lake` symlink is a self-cycle; my
  Docker build attempt hung on `mathlib: cloning` for 14+ minutes without
  reaching the cache. Closing sorries without local verification is risky.
  PR-driven CI will validate, but iteration cost is high.

## Next Action
**ACT** — implement `crossEhrhart_is_poly` via the descPochhammer construction.
The proof outline is complete; the work is wiring up the Lean syntax and
verifying lemma names (`descPochhammer_natDegree`, `descPochhammer_eval_eq_descFactorial`,
`Nat.descFactorial_eq_factorial_mul_choose`, `Polynomial.natDegree_sum_le`).

## References
- `proofs/Proofs/EhrhartCrossPolytope.lean:249-255` — `crossEhrhart_is_poly` sorry
- `proofs/Proofs/EhrhartCrossPolytope.lean:267-283` — `crossBall_card` sorry
- Mathlib: `Mathlib.RingTheory.Polynomial.Pochhammer` (descPochhammer)
- Mathlib: `Nat.cast_choose_eq_descPochhammer_div` — alternate form of the
  evaluation identity
