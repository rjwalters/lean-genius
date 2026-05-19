# Current State

**Phase**: COMPLETED
**Since**: 2026-05-04T00:19:36Z (PR #15296 merged)
**Iteration**: 4
**Last Updated**: 2026-05-17

## Status Summary

Iteration 3 axiom-elimination refactor (4 → 2 axioms via `sInf`-based
`minimalNk`) shipped and merged in PR #15296 (2026-05-04). Docker build
clean; gallery `meta.json` reflects current Lean state (lineCount 286,
axiomCount 2, theoremCount 17, definitionCount 13, sorries 0,
status `axiomatized`, badge `axiom`). The open Erdős conjecture itself
remains unresolved — the 2 standing axioms are the irreducible mathematical
content (existence witness + Martinez-Roldán-Pensado polynomial bound).

## Lean File Canonical Counts

`proofs/Proofs/Erdos827Problem.lean` (286 LOC):

| Surface       | Count |
|---------------|-------|
| theorem/lemma | 17    |
| def/abbrev    | 13    |
| axiom         | 2     |
| sorry         | 0     |

## Axiom Inventory (2)

1. `nk_exists_witness (k : ℕ) (hk : 3 ≤ k) : ∃ n, NkProperty k n`
   — existence of the threshold n_k for each k ≥ 3
2. `martinez_roldan_pensado : MartinezBound`
   — polynomial upper bound n_k ≪ k⁹ (Martinez & Roldán-Pensado correction
   of Erdős's 1978 claim)

## Theorem Inventory (17)

NEW in iter 3 (PR #15296):
- `nkProperty_nonempty` (line 89) — nonemptiness of the valid threshold set
- `minimalNk_valid` (line 96) — derived (was an axiom in iter ≤ 2)
- `minimalNk_sharp` (line 103) — derived (was an axiom in iter ≤ 2)

Unchanged from iter 2:
- `parabolaPoint_injective` (line 135)
- `parabolaSet_card` (line 145)
- `parabolaSet_gp` (line 151)
- `nk_ge_k` (line 178)
- `allDistinctCircumradii_of_card_three` (line 192)
- `nk_three` (line 223) — simplified proof in iter 3
- `nk_monotone` (line 237) — simplified proof in iter 3
- `distSq_comm` (line 249)
- `distSq_self` (line 253)
- `distSq_nonneg` (line 257)
- `distSq_eq_zero_iff` (line 261)
- `generalPosition_subset` (line 274)
- `allDistinctCircumradii_subset` (line 279)
- `nkExists_of_axioms` (line 285)

(Iter 3 state.md reported "Theorem Inventory (16)"; actual is 17. The
miscount was a manual tally off-by-one — `nkProperty_nonempty` (a
`lemma`) was listed in the NEW bullet but not added to the running total.)

## Definition Inventory (13)

`abbrev Point` (35); `noncomputable def distSq` (38); `def GeneralPosition`
(42); `noncomputable def circumRadiusSq` (51); `def AllDistinctCircumradii`
(60); `def NkProperty` (71); `def NkExists` (78); `noncomputable def
minimalNk` (86); `def ErdosProblem827` (112); `def MartinezBound` (118);
`noncomputable def erdosClaimedBound` (123); `noncomputable def
parabolaPoint` (132); `noncomputable def parabolaSet` (141).

## Open Conjecture

The Erdős problem itself (n_k for k ≥ 4) remains open. The 2 axioms above
encode the mathematical assumptions: any further axiom elimination would
require either (a) a constructive existence proof for n_k or (b) a Lean
formalization of the Martinez & Roldán-Pensado paper. Both are substantial
research projects in their own right, well outside the scope of routine
iteration.

## Blockers

None for the current state. The slug is at its honest rest-state until
new mathematics is available.

## Next Action

`COMPLETED` — no further iteration planned without external progress on
either of the 2 standing axioms. Pool flipped to `completed`; claim
released. If new mathlib lemmas (e.g., a polynomial-bound estimate for
circumradius distinctness) become available, re-open with a SCOPED phase.

## Attempt Counts

- Total attempts: 4 (iter 1 OBSERVE, iter 2 parabola GP construction,
  iter 3 sInf refactor + axiom reduction 4→2, iter 4 STATE-SYNC)
- Current approach attempts: 0 (rest state)
- Approaches tried: parabola GP construction, audit, sInf refactor,
  documentation sync

## Iteration Ledger

| Iter | Date       | Phase / Action                             | PR     |
|------|------------|--------------------------------------------|--------|
| 1    | 2026-03-28 | OBSERVE — initial Lean file + 4 axioms     | #7696  |
| 2    | 2026-04-27 | ACT — parabola GP construction; meta sync  | #13029 |
| 3    | 2026-05-04 | ACT — sInf refactor; axiom 4→2; build OK   | #15296 |
| 4    | 2026-05-17 | STATE-SYNC — docs catch up to gallery      | (this) |
