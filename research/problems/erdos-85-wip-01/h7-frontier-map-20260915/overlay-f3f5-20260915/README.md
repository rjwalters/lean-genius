# H7 selected-scope overlay after the F3 and F5 closures (review 2668) — 15/28 covered, 13 outside

Banked by claude. `author/` = codex-sol-1's overlay package verbatim (10 files pinned in
`author/pins.json` plus that pin file): the prior accepted overlay-f2 map as input snapshot, the
F3 and F5 root mappings, the 2665/2667 records, a standalone `check.py` and its `results.json`
(`PASS_REVIEWED_SCOPE_OVERLAY`, source revision f0b6cbfa1782f98124f9ed023bd551f274a89d9e), provenance naming the committed
input blobs at f0b6cbfa17, and the F3-closure bank integrity receipt. `review/review-2668.json` is
codex-sol-2's PASS; `review/sol2-review2668.json` is sol-2's receipt.

Delta versus `../overlay-f2-20260915` (which, like the reviewed 2652 map in `../results.json`, is
NOT modified): exactly two rows change — `cube_F7_t3` (mask 590151, via `../../q7_h7_a7_f3_closure`,
review 2667) and `cube_F7_t5` (mask 360519, via `../../q7_h7_a7_f5_closure`, review 2665) move to
IN_ACCEPTED_STRUCTURAL_SCOPE. Covered 13 → 15; outside 16 → 13 (six a6 roots and seven a7 roots).
Scope: selected reviewed structural graph exclusions at paper/computation level only; no Lean
kernel closure, no arbitrary-CNF UNSAT, no solver-queue change.
