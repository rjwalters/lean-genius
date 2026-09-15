# a7 F2 residual pass 1 (row/arc consistency) — FROZEN PARTIAL, F2 stays OPEN — 2026-09-15

Banked by claude. `author/` = codex-sol-2's frozen residual package: the 12 files pinned in
`author/residual-pins.json` plus that pin file, verbatim (paths as in the source package, so
`author/residual/*` holds the export, receipts, frontier, results, verification, launch and
STATUS.md, and `author/{residual.py,verify_residual.py,f2-root-mapping.json,
bank-integrity-992d0ea618.json}` sit beside them). `review/review-2658.json` is the room record
of codex-sol-1's PASS (partial evidence); `review/sol1-audit/` is sol-1's independent join /
frontier / pins audit directory (9 pinned files + `pins.json`, verbatim).

Result: one pass of the byte-identical accepted F9 residual row/arc code
(`q7_h7_a7_f9_closure/author/{batch.cpp,batch.dylib,filter.cpp}`, review 2117/2111) over the
785,408 host leaves of the COMPLETE F2 host cover (review 2657, banked in the parent directory),
120 s aggregate / 100,000 operations per leaf: 705,876 leaves visited = 705,051 INFEASIBLE_ROW +
824 INFEASIBLE_ARC + 1 UNKNOWN; 0 ARC_FEASIBLE; 79,532 leaves never attempted (exact suffix of the
export order, 2,741 groups, the first of them partial 10/32). Unresolved: 79,533 leaves, all in
source bases 82 and 93; the other 46 of 48 bases have no remaining leaf conditional on the
accepted upstream covers and these negative checks. The sole UNKNOWN (case 3710, pairing 1,
leaf 9; source 82 / singleton 1094) stopped at 104 operations in stage `generation`, which under
the pinned filter.cpp is a wall-deadline cut, not an operation-limit exhaustion (sol-2's
diagnosis, room 51254); it stays UNKNOWN in this record.

Verification: sol-2's `verify_residual.py` regenerates every negative endpoint with the 2127
reviewer's independent row enumerator (`q7_h7_a7_f9_closure/review/row-verifier/rows.{cpp,dylib}`,
pins re-checked against integration): 733,891 domains, 106,634 rows, 1,660 arc batches,
2,046 failed-support rows, PASS_NEGATIVE_RECEIPTS in 11.88 s. Sol-1 (review 2658) joined all
24,136 high inputs and 785,408 host masks to the export, confirmed the receipts are the exact
prefix, and audited pins / caps / frontier. Claude (room 51258) confirmed pins, API and verifier
identity against integration, adapter equality on all 24,136 inputs, generic (non-F9-specific)
row/arc semantics, and the recount.

Scope: necessary-condition contradictions only. No F2 (cube_F7_t2) exclusion, no H7, H1 or
Erdős 85 claim, no SAT solver, no proof replay, no Lean theorem. The room's reading of boards
#35/#36/#38 (51256/51257) is that one exactly-joined finishing slice over the 79,533 unresolved
leaves is permitted as a separately pinned pass; if it runs, it is banked separately and this
record stays immutable.
