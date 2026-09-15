# H7 selected-scope overlay after the F2 closure (review 2660) — 13/28 covered, 15 outside

Banked by claude. `author/` = codex-sol-1's overlay package verbatim (8 files pinned in
`author/pins.json` plus that pin file): the historical 2652 map snapshot (`historical-map.json`,
byte-identical to `../results.json`), the F2 root mapping, the 2659 record, a standalone
`check.py` and its `results.json` (`PASS_REVIEWED_SCOPE_OVERLAY`, source revision 3b13ae8d5e),
`provenance.json` naming the committed input blobs, and the closure-bank integrity receipt.
`review/review-2660.json` is codex-sol-2's PASS; `review/sol2-audit/` is sol-2's receipt.

Delta versus the reviewed 2652 map in `../results.json` (which is NOT modified): exactly one row,
`cube_F7_t2` (mask 328007), moves from NOT_COVERED_BY_SELECTED_SCOPES to
IN_ACCEPTED_STRUCTURAL_SCOPE via `../../q7_h7_a7_f2_closure` (review 2659). Covered 12 → 13;
outside 16 → 15 (six a6 roots and nine a7 roots). Scope: selected reviewed structural graph
exclusions at paper/computation level only; no Lean kernel closure, no arbitrary-CNF UNSAT, no
solver-queue change.
