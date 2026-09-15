# Reviewed a7 F3 evidence: q7_h7_a7_f3_closure — cube_F7_t3 excluded at paper+computation level

Accepted review 2667 (codex-sol-2, 2026-09-15). Third whole H7 root to fall today, after cube_F7_t2
(`../q7_h7_a7_f2_closure`) and cube_F7_t5 (`../q7_h7_a7_f5_closure`). `author/` = codex-sol-1's
frozen residual package, the 11 files pinned in `author/residual-pins.json` plus that pin file,
verbatim (`F3_CLOSURE.md` is the pinned pre-review candidate text; this README records acceptance;
`audit_residual.py` + `residual-verification/` are the author's own separately coded raw-source
join and endpoint verifier).

Chain: 2116 (149/149 F3 bases COMPLETE, 2,952 E/S graphs; completeness rests on the accepted
enumerator code audit, not an independent S-enumeration replay) → 2662 (66,510 high pairings) →
2664 (`../q7_h7_a7_f3_high_host_cover`: host pass COMPLETE, 4,524 negatives, 704,382 leaves) → ONE
residual row/arc pass with the byte-identical accepted 2111/2117 code
(`q7_h7_a7_f9_closure/author/{batch,filter}`), declared 180 s / 100,000 ops per leaf / 150 MB,
COMPLETE in 87.02 s: 700,062 INFEASIBLE_ROW + 4,320 INFEASIBLE_ARC = 704,382, 0 UNKNOWN,
0 unvisited, 0 retained — no finishing slice needed. Independent endpoint verification: sol-1's
`audit_residual.py` with the 2127 reviewer's row enumerator loaded from the integration checkout
(`q7_h7_a7_f9_closure/review/row-verifier/rows.dylib`; claude confirmed that file's bytes equal the
committed integration blob), 851,262 domains / 514,372 rows / 7,651 arc batches / 8,184 unsupported
rows, 33.40 s; sol-2's independent raw-source reconstruction and rerun of all 704,382 endpoints
(12.82 s) plus full host-export join (16.31 s), review 2667; claude's join (room 51340): residual
export byte-equal in order to the banked host leaves, all 704,382 receipt keys = export keys, all
negative, launch host_pins/API/driver identity.

Scope (exact): whole-shape exclusion of a7 F3 / cube_F7_t3 (mask 590151, edges 01,02,03,12,14,35,46)
at the mathematical/computational-argument level. With F2 and F5 this makes 15/28 H7 roots inside
selected structural scopes and 13 outside, pending the combined scope-overlay revision. NOT a
Lean kernel theorem, not arbitrary-CNF UNSAT, not an H7-wide, H1 or Erdős 85 exclusion; solver
queue and capped records unchanged. `review/` = room record 2667 + sol-2's review directory.
`BANK_PINS.json` = sha256 of every file here.
