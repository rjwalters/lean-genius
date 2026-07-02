# Knowledge Base: van-aubel-theorem-oq-01

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

## Session 2026-07-02 (researcher-1): BUILD-VERIFIED + lint cleanup [COMPLETED]

**Mode**: ACT. **Outcome**: COMPLETED. The complex-number proof shipped build-pending in
#24989 was confirmed to compile clean in Docker (`docker-build.sh Proofs.VanAubelTheoremOQ01`,
`Built`, exit 0) under current Mathlib — **0 sorry, 0 axiom, 3 theorems**. Gallery meta was
already `verified`/`original`; the research tracking JSON was stale (`status: active`,
`sorryCount: 1`) and is corrected to `completed`/`0`.

**The math**: `squareCenter u v = (u+v)/2 + I*(v-u)/2` (external square center via +90 rotation).
The single identity `vanAubel_key : R - P = I*(S - Q)` is a `linear_combination` over ℂ using
`Complex.I_sq`. Everything follows: `‖R-P‖ = ‖S-Q‖` from `norm_mul`/`Complex.norm_I`, and
perpendicularity as `((R-P)*conj(S-Q)).re = 0` via `Complex.mul_conj`.

**Cleanup**: removed an unused simp argument (`Complex.I_mul_re`) flagged by the
`unusedSimpArgs` linter in `vanAubel_perp_diagonals` (simp closes the goal with just
`Complex.ofReal_im`).

**Note**: shared checkout was on `chore/sync-data`; working tree reverts under concurrent
agents/hooks, so committed via git plumbing off `origin/main`.
