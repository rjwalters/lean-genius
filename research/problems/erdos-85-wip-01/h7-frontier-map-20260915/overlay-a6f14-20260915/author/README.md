# H7 selected-scope overlay 27 -> 28 (a6 F14 / cube_F6_t18, review 2718) — authored by claude

`check.py` takes the immutable 27-root map (`previous-map.json`, byte-equal to
`overlay-a6f12-20260915/author/results.json` at the revision in `provenance.json`), the F14 root
mapping (`f14-map.json`, sol-1's `root-mapping.json`: cube_F6_t18 mask 594051 <-> source F14 through
parent_to_source [2,3,4,1,0,5,6]; the checker re-derives the six mask edges and their image), and the
room record of review 2718 (`review-2718.json`, PASS whole a6 F14 necessary structural graph-cover
exclusion, codex-sol-1), and emits `results.json`: the single row `cube_F6_t18` moves to
COVERED_BY_SELECTED_REVIEWED_STRUCTURAL_SCOPE with scope F14 / review 2718; all 27 other rows,
masks and CNF identities are asserted unchanged; counts 28/28 covered, 0 residual.

The F14 closure archive is `q7_h7_a6_f14_closure` at 68ddf41f6a (receipt shard on the Stripe volume
per the 22:05Z storage rule). Third-seat recount/partition/root evidence:
`/Users/rwalters/lean-genius-h7-f14-third-seat-claude-20260915/`.

Scope: all 28 frozen H7 roots are now inside selected necessary structural graph exclusions at
paper + computation level, proof OFF; source/quotient completeness premises (2116 a7 enumerator
audit; 2118/2122/2125/2133 a6) are inherited on every row. This is not an arbitrary-CNF UNSAT
statement, not a Lean/kernel theorem, says nothing about H1, and is not a proof of the drop or of
Erdős 85. The consolidated per-root chain table is H7_CLOSURE_20260915.md (sol-1).
