# Research State: erdos-1092-oq-02

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-04T18:35:43-07:00
**Iteration**: 2

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-3, 2026-07-24) — ACT: first exact value landed

`fThreshold 1 3 = 2` machine-checked (first exact value in the family), and the
parent's removed `f_trivial_lower` axiom refuted in Lean (`fThreshold 1 4 < 3`
via K₃ + isolated vertex). File 249 → 509 lines, 13 → 21 theorems, 0 axioms /
0 sorries. Next natural rung: `2 ∈ fThresholdSet 1 4` (exact value at (1,4));
parent OQ (Rödl for r ≥ 3) remains research-level.

## Status (researcher-3, 2026-07-24, second session) — ACT: second exact value

`fThreshold 1 4 = 2` machine-checked (second exact value; file 509 → 750 lines,
21 → 26 theorems, 0 axioms / 0 sorries, docker `[8577/8577]`, headline
`[propext, Classical.choice, Quot.sound]`). Mechanism: the THREE PERFECT
PAIRINGS of Fin 4 ({01|23}, {02|13}, {03|12}) — an edge kills exactly the one
pairing putting its endpoints together; three killed pairings = three distinct
edges > budget 2 (generic `three_slots_le_card` + `slot_nonempty` helpers,
factored out of the (1,3) K₃ counting); a surviving pairing IS a 2-coloring
(3 colorings × case tree, 8 contradiction leaves + 7 survival leaves).
Constancy corollary: `fThreshold 1 3 = fThreshold 1 4` — the threshold does
not grow at the next data point (further evidence against n-1-style growth).

Next rungs: (1,5) — five pairings... no: Fin 5 has no perfect pairings (odd);
use near-pairings (2+2+1) — a surviving near-pairing 2-colors iff isolated
vertex color free; count: C(5,2)·3 = 15 near-pairings hmm; more edges available
(budget k vs 10 slots). Likely fThreshold 1 5 = 2 or 3 — compute small models
first before formalizing. Alternatively (2,4): r=2, K₄-obstruction, budget vs
6 edges, 3-colorings. Parent OQ (Rödl r ≥ 3) remains research-level.
