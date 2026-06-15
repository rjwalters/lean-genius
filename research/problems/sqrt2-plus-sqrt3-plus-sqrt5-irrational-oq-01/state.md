# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-15T18:00:00-07:00
**Iteration**: 7

## Current Focus
**Session 7 (researcher-1, 2026-06-15): BUILD GREEN — Strategy D machine-checked ✓.**
`./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01`
completed successfully (7743 jobs, 0 errors, 0 sorries, 0 axioms) — the first machine-check
after 7 build-deferred sessions. File already registered in `proofs/Proofs.lean` on main. The
S4 bearer name-check predicted green and held (no drift, no transcription risks fired). Fixed
the pre-existing gallery overclaim's stale `theoremCount` (8→10); `verified/original` is now
legitimate. Registry → status completed / phase COMPLETED / leanFiles populated. **Slug DONE.**

### Prior focus (Session 4, researcher-5)
Strategy D was **paste-port-ready** (Session 4, researcher-5). Every step of the
integral-closure descent has a Mathlib bearer **confirmed at the repo pin `v4.26.0`**: the
previously-unnamed "descent along `algebraMap ℚ ℝ`" is `isIntegral_algebraMap_iff`
(`Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:179`) and the ℤ-step is
`IsIntegrallyClosed.isIntegral_iff`
(`Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:210`). Combined with Session 3's
durable `verify_strategy_d.py` and the bound-witness recipe, no genuinely-open Mathlib gap
remains for Strategy D — only transcription. Still build-gated: Docker down (`docker info` 15s
timeout) AND Aristotle MCP `prove` returns "Resource not found" (probed this session).

## Active Approach
Strategy D — α = √2+√3+√5+√7 is a sum of algebraic integers ⇒ integral over ℤ; a rational
integral over ℤ lies in ℤ; but 8 < α < 9 ⇒ not an integer ⇒ irrational. Full bearer-confirmed
descent chain in knowledge.md Session 4. Deferred to ACT until Docker/Aristotle returns.
Fallback: Strategy A (elementary 3-squaring chain) or `m(α)=0` + rational-root theorem.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- None. Build verified green this session (Docker recovered; `lake exe cache get` works).

## Next Action
**DONE — slug verified and complete.** The proof is machine-checked and registered; gallery
meta is `verified/original` with corrected counts. Optional follow-up OQ: Strategy D scales to
any finite sum of `√(squarefree)` with no degree blow-up — the now-machine-checked reusable
criterion `irrational_of_isIntegral_of_forall_ne_int` is ready to factor into a shared gallery
√-sum irrationality helper.
