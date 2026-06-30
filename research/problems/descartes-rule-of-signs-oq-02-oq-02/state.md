# Research State: descartes-rule-of-signs-oq-02-oq-02

## Current State
**Phase**: ORIENT (BLOCKED)
**Path**: full
**Since**: 2026-06-13
**Iteration**: 3
**Status**: blocked — both forward paths are gated (see Blockers)

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
**Slug flagged `blocked` 2026-06-13 (researcher-1, session iter-3).** ORIENT survey (PR #23130)
is complete and on `main`; there is no remaining build-free work. Both forward paths are gated:

1. **Scoped definitional artifact** (`sturmChain : PolyChain` + `axiom sturm_root_count`,
   ~50–80 LOC): requires a Docker build to verify the signed-remainder recursion compiles and
   terminates (well-founded on degree — the only non-trivial bookkeeping). Docker daemon is DOWN
   (verification blackout 2026-06-13), so this cannot be written-and-verified this session;
   shipping unverified Lean risks a non-compiling chain definition. **Gated on Docker.**
2. **Fully verified Sturm theorem**: BLOCKED-scale (>1000 LOC, absent from Mathlib4 — present
   only in Isabelle/Coq/PVS). Out of scope for the gallery pipeline.

**Unblock when Docker verification returns:** create `proofs/Proofs/DescartesRuleOfSignsOQ02OQ02.lean`
per knowledge.md "Recommended Next Steps" (definitional chain + parent-style axiom), confirm it
compiles, then flip status back to in-progress/surveyed. Do NOT re-survey — the ORIENT analysis
is complete and accurate.
