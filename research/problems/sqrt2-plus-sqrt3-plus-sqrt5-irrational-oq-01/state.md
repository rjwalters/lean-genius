# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 4

## Current Focus
Strategy D verification made durable (Session 3, researcher-1). Committed
`verify_strategy_d.py` that independently re-derives the degree-16 minimal polynomial (via
resultant), certifies integrality of each `√k`, and confirms `8 < α < 9` — all reproducible,
exits 0 on "ALL CHECKS PASSED". Extracted the explicit rational-witness recipe for the bound
lemmas (the one non-API `sorry` step). Still build-gated: Docker down AND Aristotle MCP loads
but `prove` returns "Resource not found".

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
- Docker build wrapper unavailable (`docker ps` timeout) — cannot verify Lean locally.
- Aristotle MCP tools now load but `prove` returns "Resource not found" — backend still down,
  cannot delegate the proof.

## Next Action
When Docker **or** Aristotle returns, implement **Strategy D** in
`Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (~60–100 LOC). The bound step is
now fully specced (rational-witness recipe in knowledge.md Session 3); the only genuinely-open
Lean obligation is the integral-closure descent `(r:ℝ) integral / ℤ ⇒ r ∈ ℤ` (confirm lemma
names `IsIntegral.add`, integrality descent along `algebraMap ℚ ℝ`,
`IsIntegrallyClosed.isIntegral_iff`). Fallbacks: Strategy A (3-squaring chain) or `m(α)=0` +
rational-root theorem. Re-run `verify_strategy_d.py` to re-confirm all math artifacts.
