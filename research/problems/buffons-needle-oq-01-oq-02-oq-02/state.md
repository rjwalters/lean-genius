# Research State: buffons-needle-oq-01-oq-02-oq-02

## Current State
**Phase**: DONE
**Path**: full
**Since**: 2026-06-15
**Iteration**: 4

## Current Focus
COMPLETE & VERIFIED. `Proofs/BuffonConstantAsymptotic.lean` proves
`√n·c_n → √(2/π)` (`sqrt_mul_buffonConstant_tendsto`) with **0 sorry, 0 axiom**.
Machine-checked this session (researcher-3): `docker-build.sh
Proofs.BuffonConstantAsymptotic` GREEN (7743 jobs, 0 errors @ Lean v4.26.0 /
Mathlib 2df2f01). Registered in `proofs/Proofs.lean`; gallery entry
`src/data/proofs/buffons-needle-oq-01-oq-02-oq-02/meta.json` created
(status verified / badge original). Nothing left to do on the core result.

The build needed only glue repairs (no math change): add `Γ((n-1)/2)≠0` to the
`s_mul_s_succ` field_simp; drop the now-no-op `slope_def_field` rewrite (Mathlib's
`slope_mono_adjacent` returns the division form directly); remove 6 redundant
`ring`s after a now-closing `field_simp`.

## Active Approach
`s n = Γ(n/2)/Γ((n-1)/2)`; recurrence `s n·s(n+1)=(n-1)/2`; monotonicity via
log-convexity of Γ; squeeze `(n-2)/2 ≤ (s n)² ≤ (n-1)/2`; then real-analysis
packaging (`s_sq_div_tendsto`, `ratio_sq_tendsto_one`, `sq_target_eq`,
`Real.sqrt_sq` + `Real.continuous_sqrt`). All written out, no gaps.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (recurrence-squeeze)

## Blockers
- None. Docker recovered (~12:00) — builds run via the `lean-mathlib-cache`
  volume despite the circular `.lake` host symlink. Build GREEN this session.

## Next Action
- Core result DONE (verified + registered). Optional follow-ups only: extract the
  next-order term `c_n = √(2/(πn))·(1 + a/n + O(1/n²))` (numerics show the
  correction is `≈ −(√(2/π))·(c/n)` with a clean rational `c`), and/or package the
  monotone Gamma-ratio squeeze `Γ(x)/Γ(x+1/2) ~ x^{-1/2}` as a standalone lemma.
