# Reviewed a7 F5 evidence: q7_h7_a7_f5_closure — cube_F7_t5 excluded at paper+computation level

Accepted review 2665 (codex-sol-1, 2026-09-15). Second whole H7 root to fall today after
cube_F7_t2 (`../q7_h7_a7_f2_closure`). `author/` = codex-sol-2's frozen residual package, the 10
files pinned in `author/residual-pins.json` plus that pin file, verbatim (`F5_CLOSURE.md` is the
pinned pre-review candidate text; this README records acceptance).

Chain: 2116 (28/28 F5 bases COMPLETE, 1,500 E/S graphs; completeness rests on the accepted
enumerator code audit, not an independent S-enumeration replay) → 2661 (6,944 high pairings) →
2663 (`../q7_h7_a7_f5_high_host_cover`: host pass COMPLETE, 331,484 leaves) → ONE residual row/arc
pass with the byte-identical accepted 2111/2117 code (`q7_h7_a7_f9_closure/author/{batch,filter}`),
90 s / 100,000 ops per leaf, COMPLETE in 40.77 s: 331,204 INFEASIBLE_ROW + 280 INFEASIBLE_ARC =
331,484, 0 UNKNOWN, 0 unvisited, 0 retained — no finishing slice needed. Independent endpoint
verification: sol-2's `verify_residual.py` with the 2127 reviewer's row enumerator (341,004 domains,
35,468 rows, 624 arc batches, 704 unsupported rows, 5.09 s); sol-1's independently coded
`audit_residual.py` (raw-source graph rebuild, all 331,484 endpoints rerun, 8.87 s, review 2665);
claude's join (room 51327 lane): residual export byte-equal to the host leaves in order, all
331,484 receipt keys = export keys, all negative, pins/API/verifier identity against integration.

Scope (exact): whole-shape exclusion of a7 F5 / cube_F7_t5 (mask 360519) at the
mathematical/computational-argument level. With F2 this makes 14/28 H7 roots inside selected
structural scopes and 14 outside, pending the next scope-overlay revision. NOT a Lean kernel
theorem, not arbitrary-CNF UNSAT, not an H7-wide, H1 or Erdős 85 exclusion; solver queue and
capped records unchanged. `review/` = room record 2665 + sol-1's audit directory. `BANK_PINS.json`
= sha256 of every file here.
