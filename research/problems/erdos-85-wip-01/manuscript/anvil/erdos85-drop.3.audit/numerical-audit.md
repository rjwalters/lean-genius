# Numerical audit — erdos85-drop.3

Method: every numerical value in the abstract, §1, §3, §4 (incl. Tables 1–4), §5.3, §6, §7 was read against (a) the paper's own tables and cross-mentions and (b) the receipt in `erdos85-drop/refs/` the §7 list assigns to it. The deterministic numeric-consistency sibling (`erdos85-drop.3.numeric/_review.json`: 764 numbers, 0 arithmetic claims, 0 findings) was re-read; the sums below were recomputed by hand. `scope_lint.py erdos85-drop.3/main.tex` was run (read-only): its only untraced tokens are tabularx column widths (0.05 … 0.85), outline version labels (2.66–2.69) and room-transcript message numbers (31664 … 32032), none of which is a numerical claim; no Lean name missing.

Match legend: **Y** = text agrees with table/receipt; **N** = disagreement (critical flag); **~** = agrees, with a note.

## A. Internal (text vs. tables / other text)

| Text claim | Source (Tab/Fig/§) | Source value | Match | Notes |
|---|---|---|---|---|
| "two representative indices for H3, three for H5" whole-cell LRAT checks (§3.2 L146); "This is an interface description, not a claim that five whole-cell certificates are available" (L146) | §4.2 L162 "replaces the **seven whole-cell** H3/H5 formulas"; App. B L332 "reduces the **seven whole-cell** H3/H5 formulas" | 5 vs 7 | **N** | Same noun phrase, two counts. Receipt `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` §3: the seven are the cube route's *base* formulas (4 H3 scout CNFs + 3 H5 cell CNFs); the whole-cell LRAT formulas number five. Lean source confirms both counts. → `flags.md` C2. |
| "a 7×8 grid of positive cubes **per cell**" with "392 positive cubes plus fourteen negative covers … 406 bounded jobs" (L162; L332) | §4.2 L162 cells: 2 (H3) + 3 (H5) = 5 | 5 × 56 = 280 ≠ 392; 7 × 56 = 392 | **N** | 392 = 7 × 8 × 7 and 14 = 2 × 7 only if the grid is per *base formula* (seven), not per cell (five). Same root cause as above; App. B repeats it. → `flags.md` C2. |
| 1,257 = 96 + 1,161 (§1 L71; §4.2 L168) | §4.2 L168 | 96 + 1,161 = 1,257 | Y | |
| 1,416 = 96 + 1,161 + 2 + 129 + 28 (§4.2 L168) | Table 4 / §4.2 | 1,416 | Y | |
| 1,160 whole-instance + 1 cube = 1,161 (abstract, §1, §4.2, Table 4) | Table 3 outcomes 24 + 876 + 242 + 16 + 2 = 1,160 | 1,160 | Y | |
| Profile counts 283, 346, 388, 198, 42 (§4.2 L166) | sum | 1,257 | Y | |
| 1,288 = 1,158 + 96 + 34 (§4.2 L190; Table 4 L210) | — | 1,288 | Y | |
| 1,191 fresh + 96 inherited + 1 UNKNOWN = 1,288; "97 open" = 96 + 1 (L190; Table 4) | — | 1,288; 97 | Y | 1,158 − 1 (cube row) + 34 = 1,191. |
| 1,161 − 1,158 = 3 "historical object conflicts" (L190) | — | 3 | Y | Term from `PHASE_B_H1_H3_INVENTORY`. |
| 1,412 = 1,322 + 90 preparation receipts (§4.3 L219) | §1 L71 "1,412 preparation receipts" | 1,412 | Y | |
| "about 5,700 core-hours" (§1 L71) | §4.5 L229: 2,704 + 2,996 (+ 9.7 + 6.2 cube) | 5,715.9 | Y | |
| Cube tree: 71 nodes, 35 splits (31 + 4), 36 leaves, depth 8 (§4.2 L188; §4.5 L231; abstract) | Table 3 pass 4 "UNSAT through 36 cubes" | 36 | Y | |
| H7: 43 classes, 15 excluded (12 at a=6, 3 at a=7), survivors 7/12/7/2 = 28 (§4.2 L164; Table 4 L206) | — | 19+15+7+2 = 43; 7+12+7+2 = 28 | Y | |
| F14: 2,278,608 = 1,757,882 + 75,027 + 445,699 (L164) | — | 2,278,608 | Y | |
| H5 roots: 58 per cell, 15 direct certificates, 43 remaining, 129 rows (L162) | §4.2 L168 "129 H5" | 3 × 43 = 129 | Y | |
| H3/H5 cell profiles (25,18,3,0), (24,21,0,1); (14,20,10,0), (13,23,7,1), (12,26,4,2) (L162) | sizes = 49 − h; incidences = 8h; pairs = C(h,2) | 46 / 24 / 3; 44 / 40 / 10 | Y | Each row checked. |
| H7 profile 7 + 14 + 21 = 42 low vertices (L164) | 49 − 7 | 42 | Y | |
| "six named trust axioms beyond Lean's standard three" (§6 L271) | Table 1: 3 + 3 | 6 | Y | |
| "a single file of roughly 60 to 130 GB" (§4.5 L229) | 12–24 h × 5.5 GB/h | 66–132 | Y | |
| "one to four and a half weeks (8 to 32 planned days at 32 to 8 shards)" (L229) | — | 7.9–31.5 d | Y | See B. |

## B. Text vs. receipts (every value traced; all match unless noted)

| Text claim | Receipt | Receipt value | Match |
|---|---|---|---|
| Table 3 passes: pilot 24; pass 1 1,137 → 876 / 256 / 1 / 4; pass 2 261 → 242 / 19; pass 3 17 → 16 / 1; 3b 2 → 2; pass 4 1 → 36 cubes; caps 4 / 12 / 24 h; hosts | `CENSUS.md` §Passes | identical | Y |
| Six spot reclaims; $235 cloud cost (L168; §7) | `CENSUS.md` | six; $235 | Y |
| 1,413 cloud run directories + pilot (L190; §7) | `CENSUS.md` | 1,413 | Y |
| `h1_81494a6ef36d3ec9`: 42,160 vars, 613,228 clauses, sha256 860d8af2…; probe 1 h, CaDiCaL 24 h; 9.7 + 6.2 core-h; 4 h 50 min on 24 cores; hardest 0.87 / 0.96 h; 9 leaves < 10 s, 29 < 15 min; 27 of 32 in 3 s abandoned split (L188) | `CENSUS.md` §Pass 4; `cube-tree-check.json` (nodes 71, splits 35, leaves 36, max_depth 8, all UNSAT_CROSSCHECKED) | identical | Y |
| 34 outside slots, 34/34 UNSAT, Kissat 0.3–1.7 h, no cap hits, 2026-09-27/28 (L190) | `CENSUS.md` §Capacity-grid | identical | Y |
| Auditor 1,191 / 96 / 1 (L190; Table 4) | `h1-gap1288-audit.json` `counts` | 1191 / 96 / 1 | Y |
| 1,160 UNSAT_CROSSCHECKED, 1 UNKNOWN (cube), 96 historical; 2 / 129 / 28 H3/H5/H7 NOT_RUN (L168) | `h1-census-table.tsv` (1,416 rows) | identical | Y |
| 2,704 Kissat / 2,996 CaDiCaL core-h; median 1.9 h (1.88); 121 rows > 4 h; 6 rows > 12 h; 5,716 total (L229; §7) | `CENSUS_TIMING_20260928.md` | identical | Y |
| 1,412 = 1,322 historical + 90 new over four cloud passes (L219) | `CENSUS_TIMING_20260928.md` | 1,132 + 261 + 17 + 2 = 1,412; 1,322 / 90 | Y |
| Projection: 14.9 TB; 6,700 core-h; $70–100; 360 host-h; $70; 4 TB; $16/month; $2,000–2,500; 5.5 GB/h (L229, L233) | `CENSUS_TIMING_20260928.md` worksheet; `CERT_BANK_STATS_20260926.md` | identical | Y |
| 12,102 rows; 1.2 / 4.0 / 26.5 GB; 22.6 TB; ~6 TB gz; 5–6 GB per Kissat-hour in four bins (< 15 min … 4 h); 984 s per certificate; 509 MB mean, 346 MB pilot (L223, L229) | `CERT_BANK_STATS_20260926.md` | identical (bins 5,316 / 5,039 / 6,403 / 6,167 MB/h) | Y |
| 12,019 inputs; 4,831 compile box-h; 25 % noncompile; 10 % spot loss; eight bootstrap hours; 6,651 box-h; 17.32 days on 16 hosts; $1,276; 6.06 TB; $0.03/GB; $182; 48 GiB gate; 128 GiB lane (L223, L229; Table 4) | `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md` | identical | Y |
| "8 to 32 planned days at 32 to 8 shards" (L229) | `h1_replay_fleet_costs_20260910.json` `byte_weighted_planned_wall_days` | 7.88 (32 shards) … 31.48 (8 shards) | ~ (rounded) |
| 574 verified-UNSAT; 4,011 s median; 4,539 s mean; 7,102 s trim mean; 22 UNKNOWN at 14,400 s; 10.2-hour interval is pipeline time (L225; §7) | `H1_V3_SOLVER_TIMING_20260916.md` | identical | Y |
| Table 1 axiom lists; "cold rebuild 2026-09-27"; Lean 4.31.0 (L99–L113) | `AXIOM_AUDIT_COLD_20260927.md`, `axioms.out` | identical (3 + 3 native_decide axioms; Theorem B standard-only) | Y |
| h ∈ {1,3,5,7,9}; h=9 refuted; strata theorem names; f(15)=f(16)=5; `fifteenRegular`/`sixteenRegular` (L120–L127; L267) | `STRATA_AND_SMALL_ORDERS_20260928.md` | identical | Y (see note m3 in `flags.md` on "the C4-free edge bound") |
| H3: 29,500 vars, 1,328,183 clauses each; two base CNFs (L162) | `PHASE_B_H1_H3_INVENTORY_20260910.md` | identical | Y |
| H5: 58 / 15 / 43 per cell, 129; H7: 43 classes, 28 roots, 7/12/7/2 (L162, L164) | `PHASE_B_H5_H7_INVENTORY_20260910.md` | identical | Y |
| Incidence profiles; one common neighbour per high pair; support ≤ 3 (L162) | `Q7_H1_H3_SQUEEZE_20260910.md`, `Q7_H5_H7_SQUEEZE_20260910.md` | identical | Y |
| max(0, 35 − 4a); capacity 7 − 2d_E; 35 ≤ 4a + |X| (L164) | `Q7_H5_H7_SQUEEZE_20260910.md` L462–L490 | identical | Y |
| H7 ledger: 28/28 covered; A6/A7/A8/A9 routes; F14 partition; third-seat zero mismatches; enumerator-code audit caveat (L164) | `H7_CLOSURE_20260915.md` | identical | Y |
| **H7 cells t = 1,…,7** disposed of by "the H7 reduction and normalization premises the closure ledger cites as established"; Table 2 evidence for cells t=0,…,7 = "closure ledger of 2026-09-15" | `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` §1 | thirteen representatives with t ≥ 1 excluded by LRAT certificates checked in Lean (`native_decide`, 1,329,041 clauses each, manifests 2026-08-15); the ledger concerns only the t=0 cell | **N** → `flags.md` C1 |
| **H5 closure**: implied cube-grid / 129-root route with "archived local proof receipts" (L162; Table 4 L205) | same receipt §2; `H5_CLOSURE_LEDGER_README_20260910.md`; review 2065 JSONs | closure by reviewed reductions T0 (1,665→761→14→13 + 20>19), T1 (249→211→10→0), T2 (13→12 + core44/92 branches), reviews 2037/2032/2062/2063, outer 2065 PASS 2026-09-10; "no SAT run, no certificate replay"; the 129 root cubes "were not consumed" | partial → `flags.md` M1 |
| 168 edges; ten archive graphs at order 48; one 7-regular; NetworkX 3.6.1 (L158) | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `STRATA_AND_SMALL_ORDERS_20260928.md` | PASS; 10; index 9; 3.6.1 | Y |
| Six 49-vertex graphs, 174 edges, min degree 6; r(41)=49, r(42)∈{49,50}; r(s) ↔ f conversion (L65, L73, L89) | `FIRST_DROP_LITERATURE_CHECK.md` (+ its dated correction) | identical | Y |
| `v2cnf` sha256 4bd9604c…; `v2cnf emit/check` interface (L166, L219) | `PAUSE_HANDOFF_20260927.md` L29; `PHASE_B_H1_H3_INVENTORY` | identical | ~ (receipt not named in §7 — note m4) |
| App. A / §5.3: orders 64, 78, 80; 52 / 47 / 57 groups; degrees 9 / 11 / 13; 20 attempts; r(109)∈{120,121}, r(155)∈{168,169}; q=8 partitions; 80/88 owners; six Owner88 checks | `DRAFT.md` only (the adopted prior draft; BRIEF admits it as the v1 source) | identical | ~ (note m4) |
| "about 1,400 solver inputs (1,412 preparation receipts …)" (L71) | `CENSUS_TIMING_20260928.md` | 1,412 preparations of 1,161 distinct rows | ~ (note m2) |

## C. Figures

No `\includegraphics`; `erdos85-drop.3/figures/` is empty; no figure source scripts. Nothing to check for staleness (0 stale figures).

## Summary

Numerical inconsistencies: **1 root cause, 2 locations** (seven vs five whole-cell formulas; grid "per cell"), critical (`flags.md` C2). Receipt-contradicted attribution: **1** (H7 cells t ≥ 1), critical (`flags.md` C1). Everything else matches its receipt; three values trace to receipts not named in §7 (minor).
