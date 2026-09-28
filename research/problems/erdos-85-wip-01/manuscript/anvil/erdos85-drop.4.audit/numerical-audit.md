# Numerical audit — erdos85-drop.4

Method: every numerical value in the abstract, §1, §3, §4 (incl. Tables 1–4), §5.3, §6, §7 and the appendices was read against (a) the paper's own tables and cross-mentions and (b) the receipt in `erdos85-drop/refs/` that §7 assigns to it. Values unchanged from v3 were re-read against the same receipts the v3 audit used; values new in v4 (the C1/C2/M1 corrections and the reworded minors) were traced afresh. The deterministic numeric-consistency sibling (`erdos85-drop.4.numeric/_review.json`: 831 numbers, 0 arithmetic claims, 0 findings) was re-read; the sums below were recomputed by hand. `scope_lint.py erdos85-drop.4/main.tex`: PASS (66 numbers, 53 Lean names; no untraced token).

Match legend: **Y** = text agrees with table/receipt; **N** = disagreement (critical flag); **~** = agrees, with a note.

## A. Internal (text vs. tables / other text)

| Text claim | Source (Tab/§) | Source value | Match | Notes |
|---|---|---|---|---|
| Five whole-cell formulas: "two for H3 and three for H5" (§4.2 L170); "five whole-cell inputs" (§3.2 L151); "five whole-cell H3/H5 formulas of the LRAT interface" (App. B L356) | §3.2 L151: 2 + 3 | 5 | Y | v3 C2 resolved: "seven whole-cell" occurs 0 times. |
| Seven base formulas: four H3 scouts + three H5 cells (§3.2 L152; §4.2 L172; App. B L356) | 4 + 3 | 7 | Y | |
| 4 × 56 + 3 × 56 = 392 positive cubes; 8 + 6 = 14 covers; 406 jobs (§4.2 L172; App. B L356) | 224 + 168 = 392; 392 + 14 = 406 | 392 / 14 / 406 | Y | "per base formula", 7 × 8 = 56; the v3 "per cell" error is gone (0 occurrences). |
| Thirteen H7 certificates, one per representative with t ≥ 1; fourteen representatives 1,1,2,3,3,2,1,1 by t = 0..7 (Table 2 L143; §3.2 L154; §4.2 L174; §6 L292) | 1+1+2+3+3+2+1+1 = 14; 14 − 1 = 13; 1+2+3+3+2+1+1 = 13 | 14 / 13 | Y | |
| "thirteen … one for each of its canonical cells with a positive triple" (§1 L74) | Table 2 L143: cells t = 1..7 (seven), representatives 13 | 7 cells vs 13 | ~ | Count of certificates correct; the noun should be "representatives" (`flags.md` m1, minor — the number 13 is right and is glossed correctly at every other occurrence). |
| H7 t = 0: 7 + 14 + 21 = 42 low vertices; 43 classes; 12 + 3 = 15 excluded; 7/12/7/2 = 28 (§4.2 L176; Table 4 L220) | 49 − 7 = 42; 43 − 15 = 28; 7+12+7+2 = 28 | 42 / 28 | Y | |
| "eleven of the twelve a = 7 roots … and … the twelfth" (§4.2 L176) | 7/12/7/2 at a = 6,7,8,9 | 12 at a = 7 | Y | Count matches; the route wording is `flags.md` m2 (minor). |
| F14: 2,278,608 = 1,757,882 + 75,027 + 445,699 (§4.2 L176) | — | 2,278,608 | Y | |
| H5 cells: 58 roots per cell, 15 direct, 43 remaining, 3 × 43 = 129 (§4.2 L172); "129 H5 rows" (§4.2 L180; Table 4) | 58 − 15 = 43; 3 × 43 = 129 | 129 | Y | |
| H5 closure: T0 1,665 → 13; T1 249 → none; T2 13 → 12 + the 44-core with 92 branches; reviews 2037/2032/2062/2063; outer 2065 PASS 2026-09-10; three Boolean-exclusion premises (§4.2 L172; Table 2 L142; Table 4 L218) | — | — | Y | See B. |
| 1,257 = 96 + 1,161 (§1 L74; §4.2 L180); 1,416 = 96 + 1,161 + 2 + 129 + 28 (§4.2 L180) | — | 1,257 / 1,416 | Y | |
| 1,160 whole-instance + 1 cube = 1,161 (abstract, §1, §4.2, Table 4) | Table 3 outcomes 24 + 876 + 242 + 16 + 2 = 1,160 | 1,160 | Y | |
| Table 3 per-pass rows: 1,137 = 876 + 256 + 1 + 4; 261 = 242 + 19; 17 = 16 + 1; 261 = 256 + 1 + 4; 17 = 19 − 2 | — | — | Y | 19 cap hits at 12 h → 17 at 24 h plus 2 at 3b. |
| Profile counts 283 + 346 + 388 + 198 + 42 (§4.2 L178) | — | 1,257 | Y | |
| 1,288 = 1,158 + 96 + 34 (§4.2 L202; Table 4 L224); 1,191 fresh + 96 inherited + 1 UNKNOWN = 1,288; "97 open" = 96 + 1 | — | 1,288 / 97 | Y | 1,158 − 1 + 34 = 1,191. |
| 1,161 − 1,158 = 3 "historical object conflicts" (§4.2 L202) | — | 3 | Y | |
| 1,412 = 1,322 + 90 (§4.4 L233); "1,412 input preparations for the 1,161 residual rows over four cloud passes" (§1 L74; §7 L306) | Table 3: pass 1 dispatched 1,137 rows; pilot 24 rows on the Mac | 1,412 = 1,132 + 261 + 17 + 2 | ~ | The cloud preparations cover the 1,137 cloud-dispatched rows (`flags.md` m3, minor). |
| "about 5,700 core-hours" (§1 L74) | §4.6 L243: 2,704 + 2,996 (+ 9.7 + 6.2 cube) | 5,715.9 | Y | |
| Cube tree: 71 nodes, 35 splits (31 + 4), 36 leaves, depth 8 (§4.2 L200; §4.6 L245; abstract) | Table 3 pass 4 "UNSAT through 36 cubes" | 36 | Y | |
| "six named trust axioms beyond Lean's standard three" (§6 L292) | Table 1: 3 + 3 | 6 | Y | |
| "a single file of roughly 60 to 130 GB" (§4.6 L243) | 12–24 h × 5.5 GB/h | 66–132 | Y | |
| "one to four and a half weeks (8 to 32 planned days at 32 to 8 shards)" (§4.6 L243) | — | 7.9–31.5 d | ~ | Rounded; see B. |
| "thirteen order-49 inputs as five one-high cells plus one seven-high cell … four H3 scouts, three H5 cells and six H7-t0 cubes" (App. B L354) | 4 + 3 + 6 | 13 | Y | Transcript-pointer anecdote from `DRAFT.md`. |
| Table 4 "H1 residual roots … under declared caps over four passes" (L223) | Table 3: pilot, 1, 2, 3, 3b (+ 4) | five whole-instance passes incl. the pilot; "four cloud passes" elsewhere | ~ | `flags.md` n2 (nit). |

## B. Text vs. receipts (every value traced; all match unless noted)

| Text claim | Receipt | Receipt value | Match |
|---|---|---|---|
| H7 t ≥ 1: thirteen certificate modules (t,i) ∈ {(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)}; 1,329,041 clauses each; 2026-08-15 manifests with drat-trim, lrat-check and Lean replay; `native_decide` / `Lean.ofReduceBool`; not rebuilt 2026-09-27; absolute local paths (§4.2 L174; Table 2 L143; Table 4 L219; §4.4 L233; §7 L312, L321) | `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` §1 + manifest table (13 rows, 1,329,041 each, "s VERIFIED / c VERIFIED / LRAT accepted: true"); source (13 files, `include_str "/Volumes/Stripe/…"`, `native_decide` ×2 each; `…SevenHighCnf.lean` L102 `= 1329041`) | identical | Y |
| Fourteen canonical representatives, 1,1,2,3,3,2,1,1 by t; graph cover `sevenHighCanonicalGraphCover_all`; aggregate `orderFortyNineStratumExcluded_seven_of_t0` (§4.2 L174; Table 2 L143) | receipt §1; `…SevenHighCanonicalCensus.lean` L91; `…SevenHighCertificates.lean` L67–70 | identical | Y |
| H5 closure: 26 labelled → 3 canonical cells; T0 1,665 heavy classes → 13 empty negatives + 20 > 19 (review 2037); T1 249 → 0 (2032); T2 13 → 12 + core44 with 92 branches (2062/2063); outer 2065 PASS 2026-09-10, independent checker, pinned `check.py`/`results.json` hashes; "no SAT run and no certificate replay"; "the 129 root cubes … not consumed"; three Boolean-exclusion premises undischarged; checker reconstructs all 49 masks per cell (§4.2 L172; Table 2 L142; Table 4 L218) | `H5_CLOSURE_LEDGER_README_20260910.md`; `H5_CLOSURE_REVIEWED_RESULT_20260910.md`; `h5-closure-review2065.json` (resolved 2026-09-10T23:13:51Z, "PASS"); `h5-closure-reviewer-REVIEW2065.json` (heavy_cores 1665/249/13; support counts; two file hashes); receipt §2 | identical | Y |
| H5 support profiles (14,20,10,0), (13,23,7,1), (12,26,4,2); H3 profiles (25,18,3,0), (24,21,0,1) (§4.2 L170) | `Q7_H5_H7_SQUEEZE_20260910.md` L49–51; `Q7_H1_H3_SQUEEZE_20260910.md` L70–77; REVIEW2065 `support_counts` | identical; each row sums to 49 − h, incidences to 8h, pairs to C(h,2) | Y |
| H3: 29,500 variables, 1,328,183 clauses each; two base CNFs (§4.2 L170) | `PHASE_B_H1_H3_INVENTORY_20260910.md` | identical | Y |
| H5 58 / 15 / 43 per cell, 129; H7 43 classes, 15 capacity exclusions, 28 roots 7/12/7/2 (§4.2 L172, L176) | `PHASE_B_H5_H7_INVENTORY_20260910.md` | identical | Y |
| H7 t = 0 profile (seven empty, fourteen singleton, twenty-one pair), max(0, 35 − 4a), 7 − 2d_E, 35 ≤ 4a + |X|, 43 classes at a = 6..9, max degree 3 (§4.2 L176) | `Q7_H5_H7_SQUEEZE_20260910.md` L55–56, L387–L498 | identical | Y |
| H7 ledger: 28/28 covered; A6/A7/A8/A9 routes; C7 chain for `cube_F7_t14`; F12 and F14 exact partitions; F14 445,699 audited (review 2718) and reproduced by the third seat with zero mismatches; premises 1573/1574 and 2091; enumerator-code audit caveat (§4.2 L176; Table 4 L220; §4.4 L233) | `H7_CLOSURE_20260915.md` | identical, except "complement completion" applies "where required" (3 of 11 a7 rows) — `flags.md` m2 | ~ |
| Reviews 1573/1574 "also Lean theorems" (§4.2 L176) | receipt §1 last bullet; `STRATA_AND_SMALL_ORDERS_20260928.md` | as stated | Y |
| Table 3 passes: pilot 24; pass 1 1,137 → 876 / 256 / 1 / 4; pass 2 261 → 242 / 19; pass 3 17 → 16 / 1; 3b 2 → 2; pass 4 1 → 36 cubes; caps 4 / 12 / 24 h; hosts; six spot reclaims; $235 (§4.2 L180–L198) | `CENSUS.md` §Passes | identical | Y |
| Phase B index 1,416: H1 1,257 (1,160 UNSAT_CROSSCHECKED + 96 HISTORICAL + 1 UNKNOWN), H3 2, H5 129, H7 28 NOT_RUN (§4.2 L180; Table 4) | `h1-census-table.tsv` (1,416 rows; sector H1 1257 / H3 2 / H5 129 / H7 28; status 1160 / 96 / 1 / 159) | identical | Y |
| 1,413 cloud run directories + pilot (§4.2 L202; §7 L305) | `CENSUS.md` | 1,413 | Y |
| `h1_81494a6ef36d3ec9`: 42,160 vars, 613,228 clauses, sha256 860d8af2…; 1 h probe, 24 h CaDiCaL; 71/35 (31 + 4)/36/8; 9.7 + 6.2 core-h; 4 h 50 min on 24 cores; hardest 0.87 / 0.96 h; 9 leaves < 10 s, 29 < 15 min; 27 of 32 in 3 s abandoned (§4.2 L200) | `CENSUS.md` §Pass 4; `cube-tree-check.json` (nodes 71, splits 35, leaves 36, max_depth 8, all UNSAT_CROSSCHECKED) | identical | Y |
| 34 outside slots, 34/34 UNSAT, Kissat 0.3–1.7 h, no cap hits, 2026-09-27/28 (§4.2 L202; Table 4 L224) | `CENSUS.md` §Capacity-grid | identical | Y |
| Gap auditor 1,191 / 96 / 1; 97 open (§4.2 L202; Table 4 L224; §7 L305) | `h1-gap1288-audit.json` `counts`, `open: 97` | identical | Y |
| 2,704 Kissat / 2,996 CaDiCaL core-h; median 1.9 h (1.88); 121 rows > 4 h; 6 rows > 12 h; ~5,716 total (§4.6 L243; §7 L306) | `CENSUS_TIMING_20260928.md` | identical | Y |
| 1,412 = 1,322 historical + 90 new (§4.4 L233); 1,412 = 1,132 + 261 + 17 + 2 (§7 L306) | `CENSUS_TIMING_20260928.md` § Input identity | identical | Y (gloss "for the 1,161 rows": `flags.md` m3) |
| Projection: 14.9 TB; 6,700 core-h; $70–100; 360 host-h; $70; 4 TB; $16/month; $2,000–2,500; 5.5 GB/h (§4.6 L243, L247) | `CENSUS_TIMING_20260928.md` worksheet; `CERT_BANK_STATS_20260926.md` | identical | Y |
| 12,102 rows; 1.2 / 4.0 / 26.5 GB; 22.6 TB; ~6 TB gz; 5–6 GB per Kissat-hour in four bins (< 15 min … 4 h); 984 s per certificate; 509 MB mean, 346 MB pilot (§4.5 L237; §4.6 L243) | `CERT_BANK_STATS_20260926.md` | identical (bins 5,316 / 5,039 / 6,403 / 6,167 MB/h) | Y |
| 12,019 inputs; 4,831 compile box-h; 25 % noncompile; 10 % spot loss; eight bootstrap hours; 6,651 box-h; 17.32 days on 16 hosts; $1,276; 6.06 TB; $0.03/GB; $182; 48 GiB gate; 128 GiB lane (§4.5 L237; §4.6 L243; Table 4 L222) | `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md` | identical | Y |
| "8 to 32 planned days at 32 to 8 shards" (§4.6 L243) | `h1_replay_fleet_costs_20260910.json` `byte_weighted_planned_wall_days` | 7.88 (32 shards), 15.75 (16), 31.48 (8) | ~ (rounded) |
| 574 verified-UNSAT; 4,011 s median; 4,539 s mean; 7,102 s trim mean; 22 UNKNOWN at 14,400 s; 10.2-hour interval is pipeline time (§4.5 L239; §7 L309) | `H1_V3_SOLVER_TIMING_20260916.md` | identical | Y |
| Table 1 axiom lists; cold rebuild 2026-09-27; Lean 4.31.0; Theorem B standard-only; six `native_decide` axioms across the two witnesses (§3.1 L102–L119; §6 L292) | `AXIOM_AUDIT_COLD_20260927.md`, `axioms.out` | identical (3 + 3 per-declaration `native_decide` axioms) | Y |
| h ∈ {1,3,5,7,9}; h = 9 refuted; stratum theorem names; f(15) = f(16) = 5; `fifteenRegular`/`sixteenRegular` (§3.2 L123–L130; §5.3 L288) | `STRATA_AND_SMALL_ORDERS_20260928.md` | identical | Y |
| H1 structure (unique high vertex, perfect matching on its 8 neighbours, 40-vertex 6-regular remainder, eight attachment groups of five) (§4.2 L178) | `Q7_H1_H3_SQUEEZE_20260910.md` L98 | verbatim | Y |
| `v2cnf` sha256 4bd9604c…; `emit`/`check` interface (§4.2 L178; §4.4 L233) | `PAUSE_HANDOFF_20260927.md` (named in §7 L315); `PHASE_B_H1_H3_INVENTORY` | identical | Y |
| 168 edges; ten archive graphs at order 48; one 7-regular; NetworkX 3.6.1 (§4.1 L166; Table 4 L216) | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`; `STRATA_AND_SMALL_ORDERS_20260928.md` | PASS; 10; index 9; 3.6.1 | Y |
| Six 49-vertex graphs, 174 edges, min degree 6; r(41) = 49, r(42) ∈ {49,50}; r-to-f conversion and plateau ⇔ drop (§1 L68, L76; §2 L92) | `FIRST_DROP_LITERATURE_CHECK.md` + its 2026-09-28 correction | identical | Y |
| App. A / §5.3: orders 64, 78, 80; 52 / 47 / 57 groups; degrees 9 / 11 / 13; 20 attempts; r(109), r(155); q = 8 partitions; 80/88 owners; six Owner88 checks (L342–L344, L352) | `DRAFT.md` L690–L744 (the adopted prior draft); six `h305Owner88*_check` theorems in the tree | identical | Y (traceability sentence scoped, §1 L84 / §7 L303) |

## C. Figures

No `\includegraphics`; `erdos85-drop.4/figures/` is empty; no figure source scripts. Nothing to check for staleness (0 stale figures).

## Summary

Numerical inconsistencies: **0** (critical). The two v3 critical items (C1 attribution, C2 seven-vs-five) and the v3 major (M1 H5 closure) are corrected in v4 and every corrected number traces to `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md`, the four H5 ledger files, `H7_CLOSURE_20260915.md` and the Lean source. Three precision issues remain at minor level (§1 "cells" for "representatives"; §4.2 "complement completion for eleven" vs "where required"; §1/§7 "1,412 preparations for the 1,161 rows" vs the 1,137 cloud-dispatched rows) and one nit ("over four passes" in Table 4). See `flags.md`.
