# Numerical audit — erdos85-drop.5

Method: every numerical value in the abstract, §1, §3, §4 (incl. Tables 1–4), §5.3, §6, §7 and the appendices was read against (a) the paper's own tables and cross-mentions and (b) the receipt that §7 assigns to it — in `erdos85-drop/refs/` and, where the paper links a public file that has no `refs/` copy (the cuts ledger, the proof outline, the Q9 decision, the Cayley census, the budget plan, the fleet-costs JSON), the public copy on the branch worktree. Values unchanged from v4 were re-read against the receipts the v4 audit used; values whose wording changed in v5 (m1–m4, n1–n2, the R-AUD rewrites, the Appendix A pointer rows) were traced afresh. The deterministic numeric-consistency sibling (`erdos85-drop.5.numeric/_review.json`: 897 numbers, 0 arithmetic claims, 0 findings) was re-read; the sums below were recomputed by hand. `scope_lint.py erdos85-drop.5/main.tex`: PASS (65 numbers, 53 Lean names).

Match legend: **Y** = text agrees with table/receipt; **N** = disagreement (critical flag); **~** = agrees, with a note.

## A. Internal (text vs. tables / other text)

| Text claim | Source (Tab/§) | Source value | Match | Notes |
|---|---|---|---|---|
| Thirteen H7 certificates, one per representative with t ≥ 1; fourteen representatives 1,1,2,3,3,2,1,1 by t = 0..7 (§1 L85; Table 2 L162; §3.2 L173; §4.2 L193; §6 L311) | 1+1+2+3+3+2+1+1 = 14; 14 − 1 = 13 | 14 / 13 | Y | v4 m1 fixed: "thirteen canonical representatives" at L85. |
| Five whole-cell formulas (2 H3 + 3 H5) vs seven base formulas (4 H3 scouts + 3 H5 cells); 4 × 56 + 3 × 56 = 392; 8 + 6 = 14; 406 jobs (§3.2 L168–L170; §4.2 L189, L191; App. B L375) | — | 5 / 7 / 392 / 14 / 406 | Y | "never added together" retained. |
| H7 t = 0: 7 + 14 + 21 = 42 low vertices; 43 classes; 12 + 3 = 15 excluded; 7/12/7/2 = 28 roots; "eleven of the twelve a = 7 roots … (three roots) … the twelfth" (§4.2 L195; Table 4 L240) | 49 − 7 = 42; 43 − 15 = 28 | 42 / 28 / 12 | Y | v4 m2 fixed: the three roots are `cube_F7_t10/_t11/_t13` in the ledger. |
| F14: 2,278,608 = 1,757,882 + 75,027 + 445,699 (§4.2 L195) | — | 2,278,608 | Y | |
| H5: 58 roots per cell, 15 direct, 43 remaining, 3 × 43 = 129; 2 H3 rows (§4.2 L191; L199; Table 4) | 58 − 15 = 43 | 129 | Y | |
| 1,257 = 96 + 1,161; 1,416 = 96 + 1,161 + 2 + 129 + 28 (§1 L85; §4.2 L199) | — | 1,257 / 1,416 | Y | |
| 1,160 whole-instance + 1 cube = 1,161 (abstract, §1, §4.2 L199, Table 4 L242) | Table 3 outcomes 24 + 876 + 242 + 16 + 2 | 1,160 | Y | |
| Table 3 per-pass rows: 1,137 = 876 + 256 + 1 + 4; 261 = 256 + 1 + 4 = 242 + 19; 17 = 19 − 2 = 16 + 1 | — | — | Y | |
| 1,412 preparations for the 1,137 cloud-dispatched rows; 24 pilot rows; 1,137 + 24 = 1,161 (§1 L85; §7 L325); 1,412 = 1,322 + 90 (§4.4 L252) | Table 3 | 1,161 / 1,412 | Y | v4 m3 fixed. |
| Profile counts 283 + 346 + 388 + 198 + 42 (§4.2 L197) | — | 1,257 | Y | |
| 1,288 = 1,158 + 96 + 34; 1,191 + 96 + 1 = 1,288; 97 open = 96 + 1; 1,161 − 1,158 = 3 conflicts; 1,158 − 1 + 34 = 1,191 (§4.2 L221; Table 4 L243) | — | — | Y | |
| "about 5,700 core-hours" (§1 L85; §7 L325) | §4.6 L262: 2,704 + 2,996 (+ 9.7 + 6.2) | 5,715.9 | Y | |
| Cube tree: 71 nodes, 35 splits (31 + 4), 36 leaves, depth 8; 9 leaves < 10 s, 29 < 15 min (§4.2 L219; §4.6 L264; abstract; Table 3 pass 4) | 35 + 36 = 71 | 71 / 36 | Y | |
| "six named trust axioms beyond Lean's standard three" (§6 L311); "the six such entries in Table 1" (§3.1 L117) | Table 1: 3 + 3 | 6 | Y | |
| Replay: 4,831 → × 1.25 × 1.10 + 8 ≈ 6,651 box-hours; 6,651 / (16 × 24) = 17.32 days (§4.5 L256) | — | 6,650.9 / 17.32 | Y | |
| 6.06 TB × $0.03/GB ≈ $182 (§4.5 L256) | — | $181.8 | Y | |
| "8 to 32 planned days at 32 to 8 shards" (§4.6 L262) | fleet-costs JSON byte-weighted planned days: 7.88 at 32 shards, 31.48 at 8 shards | 8 / 32 | Y | rounded. |
| 2,704 h × 5.5 GB/h ≈ 14.9 TB; 12–24 h × 5.5 ≈ 60–130 GB (§4.6 L262) | — | 14.87 TB / 66–132 GB | Y | |
| Order-64 partitions of 8 into parts ≥ 2: seven listed (App. A L361) | — | 7 | Y | |
| Cayley census: 52 / 47 / 57 groups at orders 80 / 120 / 168, degrees 9 / 11 / 13; one order-48 degree-7 witness among 52 (App. A L363) | — | — | Y | |

## B. Text vs. receipts

| Text claim | Receipt | Receipt value | Match | Notes |
|---|---|---|---|---|
| Passes, rows, caps, hosts, outcomes of Table 3; six spot reclaims; $235 cloud cost; 1,413 run directories; "reviewed maximum" 24 h | `CENSUS.md` § Passes, § Phase B | identical | Y | Public copy `phase_b_h1_census_20260927/CENSUS.md` byte-identical to `refs/CENSUS.md`. |
| Cube row: 42,160 variables, 613,228 clauses, sha256 `860d8af2…`; 1 h probe, 24 h leaves; 9.7 / 6.2 core-hours; 4 h 50 min on 24 cores; hardest leaf 0.87 / 0.96 h; 27 of 32 cubes within 3 s | `CENSUS.md` § Pass 4; `tree-check.json` (nodes 71, splits 35, leaves 36, max_depth 8, all leaves UNSAT_CROSSCHECKED) | identical | Y | |
| Capacity grid 1,288 / 1,158 / 96 / 34; 34 of 34 UNSAT, Kissat 0.3–1.7 h; auditor 1,191 / 96 / 1 UNKNOWN / 97 open | `CENSUS.md` § Capacity-grid | identical | Y | |
| 2,704 / 2,996 core-hours; 1.9 h median (1.88); 121 rows > 4 h; 6 rows > 12 h; 1,412 = 1,132 + 261 + 17 + 2; 1,322 historical / 90 new | `CENSUS_TIMING_20260928.md` | identical | Y | |
| Projection: 6,700 core-hours ($70–100); 360 host-hours ($70); 4 TB ($16/month); $2,000–2,500 whole-instance | `CENSUS_TIMING_20260928.md` worksheet; `CERT_BANK_STATS_20260926.md` | identical | Y | Stated as projections, not receipts (§4.6 L266). |
| Bank: 12,102 rows; 1.2 / 4.0 / 26.5 GB; 22.6 TB; ~6 TB gz; 5–6 GB per Kissat-hour in four bins (<15 min … 4 h), projection 5.5; 984 s per certificate at 509 MB (346 MB pilot) ≈ 0.5 MB/s | `CERT_BANK_STATS_20260926.md`; `h1_replay_fleet_costs_20260910.json` (`seconds_per_certificate` 984, `reported_mean_gzip_bytes` 509000000, `pilot_gzip_bytes` 346105417) | identical | Y | |
| Replay plan: 12,019 inputs; 4,831 box-hours; 25 % noncompile, 10 % spot loss, eight bootstrap hours; 6,651 box-hours; 17.32 days on 16 hosts; $1,276; 6.06 TB; $0.03/GB; $182; 48 GiB gate; 128 GiB lane | `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md` L9, L19, L35; JSON `byte_weighted_compile_box_hours` 4831.37 | identical | Y | |
| v3 readback: 574 rows; 4,011 s median; 4,539 s mean; 7,102 s trim mean; 22 UNKNOWN at 14,400 s; 10.2 h is a pipeline interval | `H1_V3_SOLVER_TIMING_20260916.md` | identical | Y | |
| Table 1 axiom scope (Theorem B none; three `native_decide` axioms per witness; six / three for the conditional statements); cold rebuild 2026-09-27, Lean 4.31.0 | `AXIOM_AUDIT_COLD_20260927.md`; `axioms.out` (public copy byte-identical) | identical | Y | |
| H7 certificates: thirteen modules, 1,329,041 clauses each, 2026-08-15 manifests with drat-trim, lrat-check and Lean replay; `Lean.ofReduceBool`; not rebuilt 2026-09-27 | `H7_POSITIVE_TRIPLE_CELLS…_20260928.md` §1 and manifest table | identical | Y | |
| H5 closure: T0 1,665 → 13 + counting contradiction (2037); T1 249 → none (2032); T2 13 → 12 + 44-core with 92 branches (2062/2063); outer 2065 PASS 2026-09-10; three undischarged Boolean-exclusion premises; profiles (14,20,10,0), (13,23,7,1), (12,26,4,2); 49 masks per cell | `q7_h5_closure_ledger/README.md` (= `refs/H5_CLOSURE_LEDGER_README_20260910.md`); receipt §2 | identical | Y | |
| H7 t = 0 ledger: 43 classes, 15 excluded, 28 roots (7/12/7/2); A6 chain (source cover → high assignments → quotient cover); A7 2116 with 2683 on three roots; C7 → 2117; a8 normalization 2091; a9 twin6 + crossed14; premises 1573/1574/2091; F14 partition; third-seat zero mismatches; enumerator-code audit caveat | `H7_CLOSURE_20260915.md` (public copy byte-identical) | identical | Y | |
| Inventory: 129 H5 root cubes (58 per cell, 15 direct, 43 remaining), 28 H7 roots | `PHASE_B_H5_H7_INVENTORY_20260910.md` | identical | Y | |
| Witnesses: 48-vertex graph 168 edges, codegree ≤ 1; ten archive graphs at order 48 with 168 edges, one 7-regular; NetworkX 3.6.1; rerun 2026-09-28 | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`; `STRATA_AND_SMALL_ORDERS_20260928.md` | identical | Y | |
| f(15) = f(16) = 5; `sixteenRegular` 4-regular | `STRATA_AND_SMALL_ORDERS_20260928.md`; `Erdos85Problem.lean` L3638, L3826 | identical | Y | |
| r(41) = 49, r(42) ∈ {49, 50}; six 49-vertex records with 174 edges, min degree 6; conversion r(s) = min{N : f(N) ≤ N − s} | `FIRST_DROP_LITERATURE_CHECK.md` §2, §3 and 2026-09-28 correction | identical | Y | |
| App. A rows 174, 175, 176, 180; row 1; row 56; outline §A.5.3(i), §A.5.2; eleven [2,2,2,2] targets | `CUTS_LEDGER_DRAFT.md`; `FINAL_PROOF_OUTLINE.md` | identical | Y | Row 175: "uniformly for every q = 2^k, k ≥ 4" = the paper's "binary q ≥ 16". |
| App. A: 20 solver attempts UNKNOWN; two positive controls SAT; N78 open; Cayley 52 / 47 / 57 groups, degrees 9 / 11 / 13; 1 SAT among 52 at order 48 | `Q9_EXISTENCE_DECISION_20260911.md`; `CAYLEY_CENSUS_Q11_Q13_20260913.md` | identical | Y | |
| App. A: r(109) ∈ {120, 121}, r(155) ∈ {168, 169} | no receipt on disk (not in the literature note, the Cayley census file or the cuts ledger) | — | ~ | Unchanged from v3/v4; off-disk author obligation (`citation-audit.md`, `boza2024ramsey`). Not a mismatch: no receipt contradicts it. |
| App. B: 80 / 88 owners, eight fixed owners vs twelve fixed edges per shore, six 88-owner CNFs, five minutes, two minutes, a thousand sampled q = 4 models, 25 August, nearly an hour, three agents, thirteen input hashes | `refs/DRAFT.md` | identical | Y | Traces to the prior draft, which is a `refs/` file; see `flags.md` nit N2 on "thirteen input hashes". |

**Result: 0 text-vs-table mismatches, 0 text-vs-receipt mismatches, 0 untraced numbers.** No numerical-inconsistency critical flag.

## C. Figures

None; `erdos85-drop.5/figures/` is empty and there is no `figures/src/`; 0 `\includegraphics`; 0 stale figures.
