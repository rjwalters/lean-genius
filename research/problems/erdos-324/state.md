# Current State

**Phase**: COMPLETED
**Since**: 2026-03-24T15:15:41.761Z (registry graduated timestamp)
**Iteration**: 2 (S1 work T-19sessions pre-2026-03-24, S2 STATE-SYNC 2026-05-17)

## Current Focus

State.md catch-up after long-ago COMPLETED/graduated status. Open conjecture (Erdős database OPEN) in AXIOMATIZED rest-state: 1 deep axiom (`min_degree_for_distinct`) + 0 sorries, 6 of 7 original axioms eliminated via concrete counterexamples and trivial cases.

## Active Approach

None — terminal AXIOMATIZED rest-state for an open conjecture. Further reduction would require non-axiomatic proof of `min_degree_for_distinct` for general (non-power) polynomials of degree 2, 3, 4, which is itself an open problem (cf. LPS conjecture for the n ≥ 5 case).

## Blockers

None. The remaining axiom is mathematically deep and not a research blocker — it is a known open question.

## Next Action

Slug is in maintenance mode. Future iterations only if:
- A non-trivial reduction of `min_degree_for_distinct` becomes available (would require proving impossibility for general degree-2/3/4 polynomials beyond the already-covered subcases).
- A computational verification of the quintic conjecture in a bounded range becomes interesting.
- Mathlib refactors break the file or change polynomial API.

## Attempt Counts

- Total attempts: 19+ (per knowledge.md session 19 analysis; pre-registry-graduation 2026-03-24)
- Current approach attempts: 0 (post-graduation rest-state)
- Approaches tried: ≥3 (axiom elimination via counterexamples; private lemma for `card_strict_pairs`; quadratic subcase analysis)

## Lean File Inventory (canonical, matches `src/data/proofs/erdos-324/meta.json`)

| File | LOC | Theorems | Definitions | Axioms | Sorries |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos324Problem.lean` | 303 | 14 | 7 | 1 | 0 |

Status: `axiomatized` (badge `axiom`). Open conjecture remains open.

## Iteration Ledger

| Iter | Date | Type | Output |
|---|---|---|---|
| 1 (S1-S19) | 2026-01-12 → 2026-03-24 | Original research (axiom elimination) | PR #15562 (quadratic subcases), ~19 sessions documented in `knowledge.md`; reached AXIOMATIZED rest-state with 1 surviving axiom |
| 2 (S2) | 2026-05-17 | STATE-SYNC | 1 file: `state.md` NEW→COMPLETED catch-up to registry graduated 2026-03-24 (4mo stale) |

## Cross-References

- Gallery dir: `src/data/proofs/erdos-324/` (meta.json canonical: status=axiomatized, lineCount=303, theoremCount=14, definitionCount=7, axiomCount=1, sorries=0, dateUpdated 2026-05-04)
- Registry: `research/registry.json` slug "erdos-324" phase=COMPLETED, status=graduated, completed 2026-03-24T15:15:41.761Z
- Knowledge: `research/problems/erdos-324/knowledge.md` (session 19 analysis, axiom-elimination table)
- Last research PR: #15562 (research(erdos-324): prove degree-2 quadratic impossibility subcases)
