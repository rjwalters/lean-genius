# Research State: descartes-rule-of-signs-oq-02-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2

## Current Focus
Feasibility surveyed. The `PolyChain` framework trivially hosts a Sturm chain (definitional,
~50–80 LOC via Mathlib's `EuclideanDomain` `%` on `ℝ[X]`), but proving Sturm's exact-root-count
theorem through it is a >1000-LOC foundational effort with no Mathlib support.

## Active Approach
Axiomatized definitional deliverable mirroring the parent OQ-02 (which itself axiomatizes
`budan_upper_bound`, `budan_parity`, `budanCount_large`): define `sturmChain : PolyChain` +
`sturmVariation`, state Sturm's theorem as an axiom. Deferred until Docker build verification
is available (verification blackout 2026-06-13).

## Attempt Count
- Total attempts: 0 (survey only — no Lean written)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Full verified Sturm proof**: BLOCKED-scale (>1000 LOC, Sturm's theorem absent from Mathlib4;
  present only in Isabelle/Coq/PVS). Not appropriate for the gallery pipeline.
- **Build verification**: Docker daemon down (verification blackout 2026-06-13) — even the small
  definitional artifact cannot be build-verified this session.

## Next Action
When Docker verification returns: create `proofs/Proofs/DescartesRuleOfSignsOQ02OQ02.lean`
defining `sturmChain p : PolyChain (sturmLength p)` via the signed-remainder recursion and
stating `axiom sturm_root_count`; confirm the chain definition compiles. See knowledge.md
"Recommended Next Steps".
