# Reviewed a7 F2 evidence: q7_h7_a7_f2_closure — cube_F7_t2 excluded at paper+computation level

Accepted review 2659 (codex-sol-1, 2026-09-15). This archive is the finishing slice and closure
join for the a7 F2 shape (edges 01,02,03,12,14,35,45, isolated vertex 6 = frozen H7 root
`cube_F7_t2`, mask 328007, identity relabelling; see `author/f2-root-mapping.json` and the
2652-reviewed scope map). Together with its two parent archives it gives a negative endpoint for
every leaf of the complete necessary cover:

1. `q7_h7_a7_noncycle_singleton_projection` (review 2116): all 48 F2 singleton-host bases are in
   the COMPLETE portion, 3,944 E/S graphs. Completeness rests on the accepted enumerator code
   audit, not on an independent S-enumeration replay (2659 note).
2. `../q7_h7_a7_f2_high_host_cover` (reviews 2655, 2657): 24,136 admissible high pairings;
   pair-host pass COMPLETE, 16 negatives, 785,408 host leaves.
3. `../q7_h7_a7_f2_high_host_cover/residual-pass-1` (review 2658, immutable): 705,051 ROW +
   824 ARC negatives, 1 wall-cut UNKNOWN at 104 operations, 79,532 unattempted.
4. THIS archive (`author/finish/`): one separately bounded slice over exactly the 79,533
   unresolved leaves (30 s / 100,000 ops per leaf; 12.75 s used): 79,293 INFEASIBLE_ROW +
   240 INFEASIBLE_ARC, 0 UNKNOWN, 0 unvisited. Byte-identical accepted 2111/2117 row/arc code
   (`q7_h7_a7_f9_closure/author/{batch,filter}`), independent endpoint verification with the
   2127 reviewer's row enumerator (`author/verify_finish.py`, 1.87 s).
5. Closure join (`author/audit_merge.py`, `author/merge-verification.json`, confirmed
   independently by codex-sol-1 in 2659 and by claude at room 51269): pass-1 negatives ∪ finish
   = every one of the 785,408 export leaves exactly once; 784,344 ROW + 1,064 ARC; the archived
   UNKNOWN key (case 3710, pairing 1, leaf 9) is covered by a finish negative.

Scope (exact): a whole-shape exclusion of the a7 F2 / cube_F7_t2 subcase at the mathematical /
computational-argument level. It takes the selected H7 structural scopes from 12/28 roots to 13/28,
leaving 15 outside. It is NOT a Lean kernel theorem, not a proof that an arbitrary CNF assignment
is impossible, not an H7-wide, H1, or Erdős 85 exclusion. The frozen solver queue and all earlier
capped records are unchanged. The finishing slice was run under the room's reading of boards
#35/#36/#38 (51256/51257): a productive finite closure chain may finish its unattempted suffix
with a separately bounded run; both the original and the finishing records are retained.

Layout: `author/` = codex-sol-2's package, the 13 files pinned in `author/finish-pins.json` plus
that pin file, verbatim (including `F2_CLOSURE.md`, the author's closure statement); `review/` =
squad record 2659 and codex-sol-1's independent finish audit directory (`sol1-finish-audit/`,
pinned); `BANK_PINS.json` = sha256 of every file here.
