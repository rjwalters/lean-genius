# Research State: birthday-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (written, build-pending)
**Path**: full
**Since**: 2026-06-14
**Iteration**: 4

## Session 2026-06-15 (S4, researcher-5) — Pr(X=0) Schur kernel + #23219 name-check
Dual blackout still LIVE (`docker info` hangs >15s; Aristotle 404 per prior sessions).
Build-free deliverables this session:

1. **De-risked draft #23219** (the artifact gating completion). Name-checked
   EVERY Mathlib lemma it uses against the pinned v4.26.0 sibling
   (`/Users/rwalters/GitHub/mathlib4`): all current, non-deprecated —
   `div_le_iff₀`, `Finset.sum_sub_distrib`, `sum_add_distrib`, `sq_eq_zero_iff`,
   `mul_le_mul_of_nonneg_left`, `card_insert_of_notMem` (NOT the deprecated
   `_not_mem` alias), `Finset.sum_eq_zero_iff_of_nonneg`. The CS port is verbatim
   from a building ℚ file. ⟹ #23219 is name-clean; when Docker returns it should
   build and can be promoted immediately.

2. **NEW Lean: the Schur-concavity kernel** for the dual "uniform MAXIMISES
   Pr(X=0)" side, in a non-colliding companion `BirthdayProblemOQ01OQ01OQ03Schur.lean`
   (namespace `BirthdayCollisionSchur`). e_n is biaffine in any two coords:
   `g x y = A + (x+y)B + xy·C`. Proved (0 sorry, 0 axiom):
   - `biaffine_mean_sub`: `g(m,m) − g(x,y) = ((x−y)/2)²·C`  (m=(x+y)/2), pure `ring`.
   - `biaffine_le_mean` (C≥0): equalizing never decreases g — the HLP transfer step.
   - `biaffine_lt_mean` (C>0, x≠y): strict increase ⟹ uniqueness.
   - `biaffine_eq_mean_iff` (C>0): equality ⟺ x=y.
   This is the algebraic heart of N2/N3 (Schur-concavity of e_n), Python-certified
   in verify_no_collision_extremum.py. All names verified (`sq_pos_of_ne_zero`,
   `div_ne_zero`, `two_ne_zero`, `sub_ne_zero`, `mul_pos`). Build-pending UNREGISTERED.

3. Re-ran all 3 certifiers (verify_nonuniform / verify_t3_converse_certificate /
   verify_no_collision_extremum): ALL PASS.

## Current Focus
Non-uniform generalization surveyed. Precise formal target fixed:
`E[X] = C(n,2)·Σpₖ²` with the sharp result `Σpₖ² ≥ 1/d` (uniform minimizes
expected collisions, via Cauchy–Schwarz).

## Active Approach
Definitional model matching the parent's rigor (`collisionProb p = Σ (p k)²`,
`expectedCollisions n p = C(n,2)·collisionProb p`), plus the CS lower bound.
See knowledge.md "Recommended formal target (ACT plan)".

## Attempt Count
- Total attempts: 1 (ACT-1 file written)
- Current approach attempts: 1
- Approaches tried: 1 (definitional model + CS port)

## Blockers
ACT-1 IS ALREADY DONE — do NOT re-write the file. The full T1–T4 Lean file
`proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean` was written in open draft
**PR #23219** (branch `research/birthday-oq-01-oq-01-oq-03-act1`). It contains:
`collisionProb`/`expectedCollisions` defs, `collisionProb_uniform`/
`expectedCollisions_uniform` (T1), `collisionProb_ge` (T2, CS lower bound),
`expectedCollisions_ge` (T4), `collisionProb_eq_of_uniform` (T3 forward). The
CS step is a verbatim ℝ-port of `ProbMethodSecondMoment.sq_sum_le_card_mul_sum_sq`.

The remaining blocker is purely verification: the 2026-06-13/14 Docker/
`lake build` outage persists (`docker info` hangs >40s, build wrapper cannot
clear its daemon gate; confirmed 2026-06-14 by researcher-2). The file is NOT
machine-checked, so it cannot be promoted to completed yet.

## Next Action
When Docker is restored:
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`
on branch `research/birthday-oq-01-oq-01-oq-03-act1`. If green, mark PR #23219
ready-for-review and promote status to completed. The only remaining math gap
is T3's converse (equality ⟹ uniform, the CS equality case) — optional, fiddly,
and explicitly deferred per the ACT plan.
