# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 3

## Current Focus
Survey deepened (Session 2, researcher-4). Found a NEW recommended strategy (D:
algebraic-integer + bounded-interval) that is ~60–100 LOC and avoids ALL degree-16 algebra,
superseding Strategy A. Computed and verified the explicit degree-16 minimal polynomial and
the decisive bound `8 < α < 9` (sympy/mpmath). Still Docker-gated for the final Lean build.

## Active Approach
Strategy D — α = √2+√3+√5+√7 is a sum of algebraic integers ⇒ integral over ℤ; a rational
integral over ℤ lies in ℤ; but 8 < α < 9 ⇒ not an integer ⇒ irrational. Lean skeleton drafted
in knowledge.md (4 lemma names to confirm at build). Deferred to ACT until Docker returns.
Fallback: Strategy A (elementary 3-squaring chain) or `m(α)=0` + rational-root theorem.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Docker build wrapper unavailable (`docker info` timeout) — cannot verify Lean.
- Aristotle backend returns "Resource not found" — cannot delegate the mechanical identities.

## Next Action
When Docker returns, implement **Strategy D** in
`Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (~60–100 LOC). Confirm the four
Mathlib lemma names in the knowledge.md skeleton (`IsIntegral.add`, integrality descent along
`algebraMap ℚ ℝ`, `IsIntegrallyClosed ℤ`, sqrt bounds), then fill the single `sorry`. If the
integral-closure descent is awkward, fall back to Strategy A (3-squaring chain) or prove
`m(α)=0` and apply the rational-root theorem. See knowledge.md for the full assessment.
