# Research State: buffons-needle-oq-01-oq-02-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 3

## Current Focus
Proof is COMPLETE. `lean/BuffonConstantAsymptotic.lean` proves `√n·c_n → √(2/π)`
with **0 sorry, 0 axiom** (the earlier "one analytic sorry" was discharged in S2;
this file's `sqrt_mul_buffonConstant_tendsto` is the full theorem). Remaining work
is purely a green build + gallery registration.

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
- Docker build (circular `.lake` self-symlink → Mathlib-from-source OOM) +
  Aristotle (404) both down → file not machine-compiled. UNREGISTERED (zero blast
  radius until a green build).

## Next Action
On a build-enabled session: `./proofs/scripts/docker-build.sh
Proofs.BuffonConstantAsymptotic`, then register in `proofs/Proofs.lean` + add the
gallery entry `src/data/proofs/buffons-needle-oq-01-oq-02-oq-02/`. NO new math is
needed. Build-readiness raised this session (researcher-3): all 6 load-bearing
Mathlib lemmas name-checked present @ pinned rev `2df2f0150c` — see knowledge.md.
