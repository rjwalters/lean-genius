# Cayley census at q=11 and q=13 (board goal #40) — landed bundle

Report: [CAYLEY_CENSUS_Q11_Q13_20260913.md](CAYLEY_CENSUS_Q11_Q13_20260913.md).

Result: all 208 SmallGroups instances terminal (status `ALL_ATTEMPTS_TERMINAL` in
`ledger.json`, sha256 `48aa400024800c085072eedfa017caf1536a99a53dd9ecc1470031de4e6b5c5f`).
Order 48 (degree 7, positive control): 1 SAT at SmallGroup(48,26), 51 UNSAT.
Order 80 (degree 9, negative control): 52 UNSAT. Order 120 (degree 11, target): 47 UNSAT.
Order 168 (degree 13, target): 57 UNSAT. Kissat 4.0.4, seed 0, proof logging OFF,
600 s cap per group, no retries. Scope: no Cayley witness at orders 120/168 according
to proof-OFF solver reports. This is NOT an unrestricted nonexistence claim and NOT a
checked UNSAT certificate.

Provenance
- Campaign run and report rendered by codex-sol-3 (2026-09-13); on-disk sol-3 report
  was left as a mid-run snapshot when sol-3 went offline.
- Terminal ledger audit, control reviews (#2647, #2649, #2650) and the corrected
  final report by codex-sol-1 (2026-09-13, re-verified 2026-09-15).
- Independent row-by-row check of the corrected report against the terminal ledger
  (208/208 id, structure, verdict, wall) and this landing by claude (2026-09-15).

Literature (2026-09-15, codex-sol-2, reviewed PASS by codex-sol-1 as review #2651,
receipt `control-reviews/review-2651.json`): [LITERATURE_CHECK_20260915.md](LITERATURE_CHECK_20260915.md)
derives r(109) ∈ {120,121} and r(155) ∈ {168,169} from Zhang–Chen–Cheng (2017) and Boza
(arXiv:2409.12770v2), so the census question is exactly whether r(109)=121 / r(155)=169.
No exact value was found in the literature checked; the Cayley census cannot decide it.

Layout
- `ledger.json`, `manifest.json`: verbatim terminal campaign ledger and input manifest.
- `independent-reviews/`: sol-3's independent review artifacts plus `final-census.json`
  (sol-1's 208-run terminal audit, copied so the report's link resolves).
- `control-reviews/`: sol-1's audit receipts, including the standalone (48,26)
  witness description `48-26-compact.{md,json}` that needs no GAP or solver.
- `runs/48-26/`: the only SAT run, kept in full (CNF, model map, solver log, graph).
  The other 207 run directories (418 MB) and `frozen-inputs.tar.gz` (110 MB) are not
  tracked; their sha256 pins are in `frozen-inputs-pins.json`, `reproduction-pins.json`
  and per-run `input_pins` / `log_sha256` in `ledger.json`.
- `tools/`: encoder, runner, renderer, witness checker and audit scripts, plus
  `CAYLEY_ENCODING.md` (the criterion reviewed in `cayley-lemma-review.json`).
