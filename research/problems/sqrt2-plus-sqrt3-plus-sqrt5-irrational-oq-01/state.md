# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

## Current State
**Phase**: ORIENT (ACT-ready)
**Path**: full
**Since**: 2026-06-14
**Iteration**: 5

## Current Focus
Strategy D is now **paste-port-ready** (Session 4, researcher-5). Every step of the
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
- Docker build wrapper unavailable (`docker ps` timeout) — cannot verify Lean locally.
- Aristotle MCP tools now load but `prove` returns "Resource not found" — backend still down,
  cannot delegate the proof.

## Next Action
When Docker **or** Aristotle returns, **transcribe** Strategy D into
`Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (~60–100 LOC). All lemma names are
now confirmed at pin `v4.26.0` (knowledge.md Session 4): step 1 `IsIntegral.add` ×3 over
`IsIntegral ℤ (√k)` (monic `X²−C k`, `Real.sq_sqrt`); step 2 descent
`isIntegral_algebraMap_iff` (`IsIntegral/Basic.lean:179`, needs `[IsScalarTower ℤ ℚ ℝ]` +
`(algebraMap ℚ ℝ).injective`); step 3 `IsIntegrallyClosed.isIntegral_iff`
(`IntegrallyClosed.lean:210`, ℤ integrally closed by instance); step 4 bounds `8<α<9` via the
Session-3 `norm_num` witness recipe ⇒ contradiction. Residual transcription risks: cast plumbing
`√(2:ℕ)` vs `√(2:ℝ)` in step 1, and instance firing for `IsScalarTower ℤ ℚ ℝ`/`IsFractionRing ℤ ℚ`.
Fallbacks: Strategy A (3-squaring chain) or `m(α)=0` + rational-root theorem. Re-run
`verify_strategy_d.py` to re-confirm all math artifacts.
