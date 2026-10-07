# Numerical audit: erdos85-drop.8

Every number in the abstract, §§1–8, Table 1 (`tab:h1`) and Table 2 (`tab:status`) was traced to a receipt in `erdos85-drop/refs/`, to a public file on `erdos85/paper-v6` read with `git show HEAD:<path>`, or to the Lean source. The Lean source was searched with ripgrep over `proofs/Proofs/*.lean` only; nothing was built.

Totals were recomputed from the per-row TSV and JSONL receipts with Python, not copied from the summaries. The receipts were also cross-checked against each other and against the text.

**Result: 0 mismatches. 0 untraced numbers.**

The paper and Table 1 also agree with each other, since Table 1 restates §3.2 exactly. There are no figures (`\includegraphics` count is 0), so the stale-figure check does not apply.

## H1: Table 1 and §§2.4, 3, 3.1–3.4

| Text claim (line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| 13,351 orbits (abstract, L86, L123, L130, L138, L152, Tab 1, L188, Tab 2) | `oneHighCapacityInventory_total_length` (`Erdos85OneHighV2CapacityInventory.lean` L43–46); `h1_bank_check_summary.json` `coverage.capacity_orbits` | `… .sum = 13351 := by native_decide`; 13351 | yes | Partition: 12,094 + 1,160 + 96 + 1 = 13,351. Bank coverage: `bank_orbits_this_run` 12,094 + `phase_b_orbits_october` 1,257, `uncovered` 0 |
| 13,541 stored representatives, 190 removed (L123) | `PHASE_B_H1_H3_INVENTORY_20260910.md` L7 | "13,541-row raw compact inventory … 13,351-row capacity-filtered universe" | yes | 13,541 − 13,351 = 190 |
| one of five profiles; miss table of 24 counts (L121) | `Erdos85OneHighV2CapacityInventory.lean` (`List.finRange 5`); `Erdos85OneHighV2Inventory.lean` L12 | 5 profiles; `values_length : values.length = 24` | yes | |
| hardest orbit: 42,160 variables, 613,228 clauses (L121) | `CENSUS.md` L42 | "(42,160 variables, 613,228 …" | yes | |
| 23 `native_decide` axioms + propext, Classical.choice, Quot.sound; no `sorryAx` (L130, Tab 2) | `H1_COVER_AXIOMS_20261006.txt` | 23 distinct `…native_decide.ax_*` names in the list for `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`; header "no sorryAx" | yes | Counted by hand from the printed list: 19 `ax_1_1` declarations plus `oneHighStandardMate_even_pair` `ax_1_1`…`ax_1_4` |
| 1,161 orbits with no August certificate (L132, L174) | `CENSUS_TIMING_20260928.md` L15; bank README | Total 1,161; "1,161 residual roots" | yes | 1,161 = 1,160 + 1 |
| census about 5,700 core-hours (L132) | `CENSUS_TIMING_20260928.md` L28 | "about 5,716 core-hours" | yes | |
| Kissat 4.0.4, CaDiCaL 3.0.1 (L132, L174, Tab 1) | `CENSUS.md`; `h1_cert_census_summary.json` `solver.version` | 4.0.4; 3.0.1 | yes | |
| about 28 TB in all (abstract, L86, L138, Tab 1) | bank `lrat_bytes_total` + census `proof_bytes_total` + historical Σ`lrat_bytes` + leaf Σ`lrat_bytes` | 22.554 + 5.641 + 0.103 + 0.047 = 28.345 TB | yes | Summed from receipts |
| bank: 12,094 orbits, 22.55 TB, largest 26.5 GB, 8 GB heap (Tab 1, L138, L172) | `h1_bank_check_receipts.tsv` (12,094 rows) | Σ`lrat_bytes` 22,554,276,624,018; max 26,521,722,365; `heap_mb` 8000 on all 12,094; `status` VERIFIED on all 12,094 | yes | TSV recomputation equals the summary JSON |
| bank: 6.29 TB compressed; 408 hours of summed check time (L172) | TSV Σ`gz_bytes`; summary `check_wall_hours_sum` | 6,285,686,522,598; 408.5 | yes | |
| one orbit with no producer ledger line (L172) | summary `no_producer_ledger_rows` | [`0051c0f06f824a2e`] | yes | |
| twenty-one CNF-mismatch runs, one reclaimed machine (L172) | summary `ledger_statuses.CNF_MISMATCH`, `cnf_mismatch_note` | 21; "spot node … being reclaimed" | yes | |
| bank proofs from Kissat DRAT via drat-trim, compacted (Tab 1, L172) | `CERT_BANK_STATS_20260926.md` L3; bank README "Method" | `solve_s` (Kissat seconds), `drat_bytes`, `raw_lrat_bytes`, `compact_bytes`; "drat-trim LRAT … `compact_h1_v2_lrat.py`" | yes | |
| census: 1,160 orbits, 5.64 TB, largest 36.2 GB, 4–16 GB heap (Tab 1, L174) | `h1_cert_census_receipts.tsv` (1,160 rows) | Σ`proof_bytes` 5,640,561,168,915; max 36,165,375,193; `heap_mb` {4000: 1075, 8000: 72, 12000: 1, 16000: 12} | yes | |
| 4 GB sufficed for 1,075 of 1,160; none needed more than 16 GB (L148) | same TSV | 1,075 at 4000 MB; max 16000 | yes | |
| checking about 6% of solver CPU time (L148) | summary `checker_cpu_hours` / `solver_cpu_hours` | 207.1 / 3,434.7 = 6.03% | yes | |
| 3,435 solver and 207 checker CPU-hours (L174) | TSV Σ cpu seconds / 3600 | 3,434.73; 207.09 | yes | |
| 1,157 Graviton + 3 Apple-silicon (L174) | TSV `instance_type` | r8g 459 + r7g.16xl 432 + r6g 263 + r7g.4xl 3 = 1,157; Mac 3 | yes | |
| CaDiCaL binary sha256 `fd601b82…`, cake_lpr sha256 `95b64883…`, commit `a36874a8` (L145, L174) | census summary `solver`, `checker` | `fd601b82…72a2`; `95b64883…f00c`; `a36874a8…` | yes | The bank summary gives the same commit `a36874a8` |
| 1,196 run records = 1,163 verified (three orbits twice) + 33 faults (L174) | census summary `ledger_statuses`; TSV `certified_copies` | 1,163 CERTIFIED + 30 ERROR + 3 SOLVER_NOT_UNSAT = 1,196; `certified_copies` = 2 for 3 rows | yes | |
| three orbits solved twice gave identical proofs of 27 to 28.6 GB (L146) | census summary `determinism_pairs`; TSV `proof_bytes` | 3 pairs `identical: true`; 27.17, 28.08, 28.59 GB | yes | |
| historical: 96 orbits, all accepted by cake_lpr build `d23c413b`, 0.10 TB, largest 2.49 GB (Tab 1, L176) | `h1_cert_historical96_cake_lpr_receipts.jsonl` (96 rows) | `status` CAKE_LPR_VERIFIED ×96; `checker_sha256` `d23c413b…` ×96; `cake_lpr_rc` 0 and `drat_trim_rc` 0 ×96; Σ`lrat_bytes` 103,469,269,771; max 2,494,722,547 | yes | |
| same sha256 as the earlier conversion pass (L176) | per-tag join with `h1_cert_historical96_receipts.jsonl` (accepted rows) | 0 of 96 differ | yes | |
| 50 historical + 30 cube leaves also accepted by `LRAT.check` (L176) | `h1_cert_historical96_receipts.jsonl`; `pilot_h1_81494a_leaf_std_lrat_check.jsonl` (public, paper-v6) | LRAT_CHECK_ACCEPTED 50 (+46 CAKE_LPR_VERIFIED, 2 superseded OOM); 30 LRAT_CHECK_ACCEPTED | yes | |
| hardest orbit: 36 leaf cubes, depth at most 8 (L180) | `cube-tree-check.json` | `leaves` 36, `max_depth` 8, `splits` 35, `nodes` 71 | yes | |
| caps of up to 24 hours (L180) | `DRAFT.md` L95/L216 | "failed every whole-instance cap up to 24 hours" | yes | |
| 36 leaves, 47.1 GB, largest 8.24 GB, 4 GB heap, cake_lpr `d23c413b` (Tab 1, L182) | `pilot_h1_81494a_leaf_cake_lpr.jsonl` (36 rows) | Σ`lrat_bytes` 47,066,436,918; max 8,237,398,299; `heap_mb` 4000 ×36; `checker_sha256` `d23c413b…` ×36; CAKE_LPR_VERIFIED ×36 | yes | |
| macOS CaDiCaL for the leaves; each leaf CNF hash-checked (L182) | `pilot_h1_81494a_leaf_solves.jsonl` (public); `solve_leaves.py`, `backfill_leaf_receipts.py` | `command[0]` = `/opt/homebrew/bin/cadical`; 31 rows `cube_sha_ok: true`; 5 rows from `solve_leaves.py`, which returns `CUBE_SHA_MISMATCH` without solving on a mismatch | yes | |
| proof sha256 only for the 30 smaller leaves (up to 2.42 GB) (L182) | `pilot_h1_81494a_leaf_std_lrat_check.jsonl`; leaf size ranks | 30 rows with `lrat_sha256`, max `lrat_bytes` 2,419,876,486 = 30th-smallest leaf; cake_lpr and solve receipts have no proof hash | yes | |
| composition: four statements, `propext` and `Quot.sound` only (L184) | `COMPOSITION_AXIOMS_20261006.txt` | 4 × `[propext, Quot.sound]` | yes | |
| about $225 for the census and the bank re-check (L188) | census README "≈ $204"; bank summary `cloud_spend_usd_estimate` 20.42 | 224.42 | yes | Scoped exactly; no cost receipt exists for the historical pass |
| ami-05697724475f2e748, us-east-1, 12,094 bank proofs, Requester Pays (L262) | `CHECKING.md` (public, paper-v6) Steps 1–2, Files | identical | yes | |

## Lower sides, case split and small strata (§§2.1–2.3)

| Text claim (line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| 48-vertex witness 7-regular with 168 edges (L94) | `DRAFT.md` L90 | "168 edges, all pair codegrees ≤ 1" | yes | 48·7/2 = 168 |
| three per-declaration `native_decide` axioms per witness, beyond the 3 standard (L94, Tab 2) | `axioms.out` | `boza48Graph` ×3 and `orderFortyNineDegreeSixGraph` ×3 | yes | |
| Theorem B uses the three standard axioms only (L94, Tab 2) | `axioms.out` L1 | `[propext, Classical.choice, Quot.sound]` | yes | |
| not isomorphic to any of ten 48-vertex 168-edge Afzaly–McKay graphs (L94) | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt` | "non-isomorphic to all 10 Afzaly--McKay archive graphs" | yes | |
| Lean 4.31.0 cold rebuild (L94, Tab 2 caption) | `AXIOM_AUDIT_COLD_20260927.md` L12–13 | `lean4-arm64:v4.31.0`, Lean `4.31.0` | yes | |
| Σ(deg u − 1) ≤ 48; h ∈ {1,3,5,7,9} (L98) | arithmetic; `orderFortyNine_card_high_eq_…_nine` (exists) | 49 − 1 = 48; 7·49 + h even ⇒ h odd | yes | |
| H3: two cells t=0,1; 29,500 variables, 1,328,183 clauses (L111) | `PHASE_B_H1_H3_INVENTORY_20260910.md` L19; `H7_POSITIVE_…` L55 | "29,500 variables, 1,328,183 clauses" | yes | |
| H5: three cells; 49 masks per cell; T2: 13 heavy → 12 excluded → 92 branches (L113) | `H5_CLOSURE_LEDGER_README_20260910.md` L7, L13; `H7_POSITIVE_…` L46 | "all49 masks"; "13 heavy classes→12 excluded … whose92 branches" | yes | |
| H7: t ≤ 7; fourteen representatives, thirteen with t ≥ 1; 1,329,041 clauses each (L115) | `H7_POSITIVE_…` L9, L11, L21–L33 | "fourteen representatives, distributed 1,1,2,3,3,2,1,1 by t = 0..7"; 13 rows at 1,329,041 | yes | |
| t=0: 42 low = 7 + 14 + 21 (L117) | arithmetic | 49 − 7 = 42 = 7 + 14 + 21 | yes | High-incidence count 14·1 + 21·2 = 56 = 7 high × 8 neighbours |
| 43 classes, 15 excluded by counting, 28 by the ledger (L117) | `H7_CLOSURE_20260915.md` L11 | "43 classes … excludes 15 and retains exactly these 28 (7/12/7/2 for a=6/7/8/9)" | yes | "6 to 9 edges" matches the retained a = 6..9 split. The edge range of the 15 excluded classes is not separately printed (minor traceability gap, no conflict) |
| 2,278,608 leaves; final 445,699 certificates reproduced by a third implementation, no mismatch (L117) | `H7_CLOSURE_20260915.md` L67 | "2,278,608 host leaves partition as 1,757,882 + 75,027 + 445,699 … third-seat independent implementation … all 445,699 certificates … zero mismatches" | yes | |
| completeness of one source enumeration rests on an enumerator-code audit (L117) | `H7_CLOSURE_20260915.md` L20 | "2116 completeness rests on an accepted enumerator-code audit" | yes | |

## Theorem B, evidence and negative map (§§1, 5, 6)

| Text claim (line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| r(41)=49; r(42)∈{49,50} (L76) | `FIRST_DROP_LITERATURE_CHECK.md` L56–57 | same | yes | |
| f(15)=f(16)=5; `sixteenRegular` 4-regular C4-free on 16 vertices (abstract, L229) | Lean declarations (`minDegreeForC4_fifteen`, `_sixteen`, `sixteenRegular_degree`, `sixteenRegular_common_le_one`) present | — | yes (names) | Statement values not re-elaborated (grep only) |
| q=8 partitions [3,3,2], [4,2,2], [6,2], [4,4], [5,3], [8] (L239) | `DRAFT.md` L690–697 | same lists and statuses | yes | |
| order-80 search: UNKNOWN in all 20 attempts (L240) | `DRAFT.md` L705–706 | "All 20 … q9 solver attempts ended UNKNOWN" | yes | |
| Cayley census 52 / 47 / 57 groups of orders 80 / 120 / 168 (L240) | `DRAFT.md` L713–714 | same | yes | |
| r(109)∈{120,121}, r(155)∈{168,169} (L240) | `DRAFT.md` L724 | same | yes | |
| P8 survived a thousand sampled q=4 models (L236) | `DRAFT.md` L587 | "a thousand sampled q=4 models" | yes | |
| 80 owners instead of 88 (L249) | `DRAFT.md` L449, L520 | "used 80 owners, but … required 88" | yes | |
| half-integral survivor at q=6; cuts ledger row 175 (L238) | `DRAFT.md` L366, L414 | same | yes | |
| abstract ≤ 1,920 characters (R-V8 §5) | `pdftotext` of the fixpoint PDF, Abstract → §1 | 1,767 | yes | |

## Deterministic tools

- `scope_lint.py erdos85-drop.8/main.tex --refs erdos85-drop/refs --proofs …/proofs/Proofs`: **PASS** (34 numbers checked, 39 Lean names checked).
- `erdos85-drop.8.numeric/_review.json` (reviewer-run `numeric_consistency`): 0 findings over 312 numbers.
- Lean identifiers: ripgrep over `proofs/Proofs/*.lean` (≤ 5 MB files) for declaration-shaped matches found 47 of 47 `\lean{}`/`\leantab{}` declaration names. The remaining tokens are not declarations: `hno49` is a binder in `Erdos85FiniteDropCore.lean` L31; `h1_81494a6ef36d3ec9` is an orbit tag; `#1`, `#2` and `tt` are macro artefacts. `PlaneOrderDropWitness.strict_drop` matches in 2 files.

## Figures

None. `figures/` is absent and the paper has no `\includegraphics`, so there are 0 stale figures.
