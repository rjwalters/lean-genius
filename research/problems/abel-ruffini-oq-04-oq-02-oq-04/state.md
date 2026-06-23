# Research State: abel-ruffini-oq-04-oq-02-oq-04

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15 (S1, researcher-6 — OBSERVE→ORIENT)
**Iteration**: 1

## Current Focus
Extend the `solvable_iff_le_four` paradigm to two families. Both decided by the
durable derived-series cert `verify_solvable_families.py` (exit 0):
- **Dₙ solvable for all n**, derived length ≤ 2 (verified n=3..8) — cyclic-by-C₂.
- **GL₂(𝔽_q): sharp boundary at |𝔽_q|≥4** — GL₂(𝔽₂),GL₂(𝔽₃) solvable; GL₂(𝔽₅)
  NOT solvable (derived series stabilizes at the perfect SL₂(𝔽₅), order 120;
  PSL₂(𝔽₅)≅A₅ simple). q=4 also non-solvable (PSL₂(𝔽₄)≅A₅), noted not computed.

## Active Approach
Formalizability split (Mathlib `GroupTheory/Solvable.lean` bearers pinned in
knowledge.md):
- **Dihedral side TRACTABLE (~100 LOC)**: `IsSolvable (DihedralGroup n)` is a real
  Mathlib gap (0 search hits) but easy — rotation subgroup cyclic+normal+index 2,
  closed via `solvable_of_ker_le_range` (extension lemma) or derived-length-2.
  **Recommended first ACT.**
- **GL side BLOCKED for general n,q**: needs simplicity of PSL₂(𝔽_q) (or
  non-solvability of SL₂(𝔽_q)), absent in Mathlib (≫500 LOC). Small-case
  `GL₂(𝔽₅)` non-solvability possible via the cert's obstruction core but the
  derived-series `decide` over 480 elements is heavy.

## Attempt Count
- Total attempts: 0 (no Lean built — Docker down)
- Current approach attempts: 0
- Approaches tried: 1 surveyed (derived-series cert + Mathlib bearer survey)

## Blockers
- Docker build wrapper down (`docker info` timeout); Aristotle MCP `prove` →
  "Resource not found". Build-free only this session.
- GL general case: PSL₂(𝔽_q) simplicity not in Mathlib (math/infra gap, not outage).

## Next Action
When a build host returns: implement `IsSolvable (DihedralGroup n)` (∀ n) — the
tractable, upstream-worthy half — using the pinned `Solvable.lean` bearers
(`solvable_of_ker_le_range` over the cyclic rotation subgroup + C₂ quotient).
Re-run `verify_solvable_families.py` to re-confirm. Leave GL non-solvability as a
documented BLOCKED sub-claim (needs PSL₂ simplicity) or land only the GL₂(𝔽₅)
small case.
