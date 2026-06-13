# Research State: birthday-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 3

## Current Focus
ACT-1 written: `proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean` (new file,
namespace `BirthdayDistributionNonUniform`, `import Mathlib`). Implements the
T1–T4 plan from knowledge.md as a self-contained definitional model matching the
parent's rigor. **Build-pending** — written during the 2026-06-13 Docker outage,
shipped as a DRAFT PR (not machine-checked yet).

## Active Approach
- `collisionProb p = ∑ k, (p k)²`, `expectedCollisions n p = C(n,2)·collisionProb p`.
- T1 `collisionProb_uniform`: uniform `p ≡ 1/d` ⟹ `collisionProb = 1/d`
  (+ `expectedCollisions_uniform = C(n,2)/d`).
- T2 `collisionProb_ge`: Cauchy–Schwarz lower bound `1/d ≤ collisionProb p`.
  CS step is a **verbatim port over ℝ** of
  `ProbMethodSecondMoment.sq_sum_le_card_mul_sum_sq` (induction + `sub_sq` + `nlinarith`).
- T4 `expectedCollisions_ge`: `C(n,2)/d ≤ expectedCollisions p n`.
- T3 `collisionProb_eq_of_uniform`: forward direction only; CS equality-case
  converse deferred per the ACT plan.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
ACT file is written but cannot be machine-checked: the 2026-06-13 Docker /
`lake build` verification outage persists (`docker info` down) and the Aristotle
backend returns 404. Residual risk is confined to Mathlib v4.26 lemma-name /
API surface (e.g. `div_le_iff₀`, `nsmul_eq_mul`, `Finset.card_univ`) — all
build-surfaced, hence the DRAFT.

## Next Action
When Docker/verification is restored: build via
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`, fix any
v4.26 API drift, un-draft the PR, then promote status to completed. Optional
stretch (beyond OQ closure): the T3 CS equality-case converse and a genuine
product-PMF expectation derivation of E[X].
