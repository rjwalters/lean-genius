# Numerical audit: erdos85-drop.10

**Method.** Every number in text that is new or edited in v10 (abstract, Result A, §1, §2.2, §2.3 H3/H5/H7 and "The H7 certificates", §3 hexagon paragraph, §3.4, Table 2, post-table paragraph, §7, §8) was traced to two places: a thread ref in `erdos85-drop/refs/`, and the receipt linked at the pinned commit `1d0772cd825462f5230f224c2110231c6483d5e4` (read with `git show`). The Lean facts were checked by reading source at the pin, extracted with `git archive` into a scratch directory; nothing was built. The H1 core totals were recomputed again from the per-row receipts. Numbers carried unchanged from v9 were confirmed to appear verbatim in v9 and v10 (same occurrence counts) and were fully traced in `erdos85-drop.9.audit/` and `erdos85-drop.8.audit/`. Other checks that agree: `scope_lint.py --proofs <pin>/proofs/Proofs` PASS (39 numbers, 46 Lean names); the `.10.numeric` sibling (380 numbers, 0 findings); codex's Decimal re-summation of all 13,094 H7 result files (`erdos85-drop.10.independent/independent-totals.json`, equal to `campaign_totals.json` in every bucket).

## New or edited numbers (v10)

| Text claim (main.tex line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| "into four strata" (abstract L66) | §2.2 L97; `orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine` | five values h∈{1,3,5,7,9}; h=9 refuted | **no (minor m1)** | Internal inconsistency in wording, not in data. Four *remaining* strata. |
| H7 t=0: 28 cover + 377,776 leaf formulas (L66, L78, L123) | `refs/h7_collected_summary_20261011.json` totals; pin `receipts/collected/summary.json` | 28 cubes; `leaves` 377,776; `certified_leaves` 377,776; `missing_leaves` 0 | yes | Count at symmetry-breaking depth 3 (`leaves 3 mask`, README L229); the capstone takes `(depth : Nat)` (minor m2). |
| 377,804 formulas (L85, L153, Table 2 L225) | 28 + 377,776 | 377,804 | yes | Table 2 "377,804 refutations accepted": 377,803 direct plus 1 through 257 split formulas (minor m4). |
| 377,775 leaves + 257 split formulas verified (L132) | `campaign_totals.json` `leaf:CERTIFIED` 377,775, `split:CERTIFIED` 257; summary `split_leaves` 1; pin `split-pass-manifest.jsonl` 257 rows | as stated | yes | |
| 232 residual leaves at 12 h; one leaf hit 12 h (L132) | pin `residual-pass-manifest.jsonl` 232 rows; `leaf:SOLVER_TIMEOUT` 233 = 232 + 1 | yes | yes | "the 233 that hit a cap and were re-run" (L132): 232 were re-run and 1 was split (nit N1). |
| 2-hour main cap; 12-hour residual cap; Graviton (L132) | `refs/H7_HSB_CAMPAIGN_README_20261011.md` L19, L534, L553 | 2 h cap; 12 h residual cap; r8g/r7g.16xlarge Graviton | yes | |
| 256 sub-leaves; lookahead on edge variables (L132) | README L632; split manifest 257 = 256 + 1 sub-cover | yes | yes | |
| 4,269 solver / 706 checker CPU-h, ~20.2 TB (leaf + split, no covers/superseded) (L132) | summary totals 4,268.71 / 705.74 / 20,210,589,568,747 B (= leaf 4,264.81 + split 3.89; 705.12 + 0.60; bytes sum exact) | yes | yes | Abstract "20 TB for H7" (L66) matches. |
| 4,711 solver / 740 checker CPU-h, every run (L132) | `campaign_totals.json` `all_runs` 4,711.11 / 740.44; 378,293 runs = 28 + 377,775 + 233 + 257 | yes | yes | Codex re-summed all 13,094 files with the same result. |
| **"about \$215 of cloud compute" (L132)** | linked `campaign_totals.json` (pin) = `refs/h7_campaign_totals_20261011.json`: **no cost field**. Pin `h7_hsb_campaign_20261008/README.md` = `refs/H7_HSB_CAMPAIGN_README_20261011.md`: pre-run estimates only ($68 spot point, $160 hard stop). No file in `refs/` contains \$215. | Found only in post-pin commit `d56328ec42b` README L9–10: "Cost (controller-reported estimates, not billing totals): main \$125.24, residual \$81.99, split \$1.53, plus about \$6 … about \$215 in all" (sum 214.76) | **untraced at the linked receipt and in refs/ (critical C2)** | Arithmetic is right once the post-pin source is used. The paper drops the "controller-reported estimate" qualifier. |
| 17,633 variables, 720,825 clauses (L123) | README L26, L30, L42 | `p cnf 17633`; 720,825 clauses | yes | |
| solver `fd601b82…`, checker `4d47ffdd…` (L132) | README L71–72, L279 | yes | yes | The checker is the builder build of commit `a36874a8`, a different binary from H1's fleet build `95b64883…` (nit N4, L203 "same trusted base"). |
| 43 classes, 6–9 edges; 15 counting by kernel `decide`; 28 structural (L123) | pin `Erdos85OrderFortyNineSevenHighT0EmptyCountingCore.lean` L19–20 ("kernel `decide` (no `native_decide`)"), L189 `sevenHighT0CountingCertificates_hold`; 28-entry `sevenHighT0StructuralCubes`; review's 19+15+7+2 | yes | yes | |
| h=9: 18 representative certificates by `native_decide` (L97, Table 2 L218) | pin `Erdos85OrderFortyNineNineHighContradiction.lean`: 19 imports, 18 `…Certificate` modules, relative `include_str` | 18 | yes | |
| 601 = 3 + 598; corollaries 607 (3 + 604), 604 (3 + 601); no `sorryAx` (L66, L111, L153, Table 2 L226) | `refs/RELEASE_ASSEMBLY_README_20261011.md` L42, L67–68; `refs/ORDER49_H3_CLOSED_CAPSTONE_README_20261008.md` L4, L16, L103 | identical | yes | |
| 891 imported modules; "not a cold rebuild" (L111, Table 2 L226) | release README L38, L44–45, L69; capstone README L35 | "all 891 imported object hashes matched"; "not a cold rebuild of all native certificates" | yes | Independently confirmed: the import closure of `Erdos85OrderFortyNineCapstoneH3` at the pin has 892 modules (891 + wrapper). |
| H3: 408 parts (24 + 384); three standard + 408 native (L117, Table 2 L221) | `refs/H3_STRATUM_INTEGRATION_README_20261008.md` L4, L31–32 | "24 pair native axioms, 384 triple native axioms, and propext, Classical.choice, Quot.sound (411 total)" | yes | |
| H5: 40 search parts plus graph-cover and cardinality checks (L119, Table 2 L222) | `refs/H5_TERMINAL_REVIEW_README_20261008.md` L3–12, L57–59 | 61 = 3 + 40 native search + 18 reviewed graph-cover axioms; the cover sites prove "fiber counts, representative array lengths … triple-support count"; status `H5_STRATUM_ARTIFACT_AUDIT_PASS` | yes | "Cardinality checks" is a fair paraphrase. The count 18 is not given (review n4). |
| 23 `native_decide` axioms for H1 (L145, L153, Table 2 L219) | `refs/H1_COVER_AXIOMS_20261006.txt` | 3 + 23 | yes | unchanged from v9 |
| 13 H7 t≥1 certificate modules (L121, Table 2 L223, L285) | pin import closure: exactly 13 modules with absolute `include_str` (`…SevenHighT{1..7}Rep*Certificate`); `refs/CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json`: 13 reads, 2,574,916,357 B in all, largest 1,606,429,555 B | 13 | yes | The count matches; the consequence is M1. |
| abstract ≤ 1,900 characters (R-V8) | `pdftotext` of fixpoint PDF | ~1,712 rendered characters | yes | |
| 14 pages; references from p. 12 (main text 11 pp) | fixpoint build | 14; "References" on p. 12 | yes | R-SIMPLE target ~10 pp (review m8). |

## H1 core totals (recomputed this run from per-row receipts; unchanged text)

| Text claim | Source | Recomputed | Match |
|---|---|---|---|
| 12,094 bank orbits; 22.55 TB; largest 26.5 GB; 6.29 TB compressed (Table 1, L187) | `h1_bank_check_receipts.tsv` (12,094 rows, all `VERIFIED`) | Σ`lrat_bytes` 22.554 TB; max 26.52 GB; Σ`gz_bytes` 6.286 TB | yes |
| 1,160 census; 5.64 TB; largest 36.2 GB; 3,435 / 207 CPU-h (L178, L189) | `h1_cert_census_receipts.tsv` (1,160 rows, all `CERTIFIED`) | 5.6406 TB; 36.17 GB; 3,434.7 / 207.1 | yes |
| historical 96; 0.10 TB; largest 2.49 GB; all cake_lpr (L179, L191) | `h1_cert_historical96_cake_lpr_receipts.jsonl` (96, all `CAKE_LPR_VERIFIED`) | Σ`lrat_bytes` 0.1035 TB; max 2.495 GB | yes |
| hardest orbit: 36 leaves, 47.1 GB, largest 8.24 GB (Table 1, L197) | `pilot_h1_81494a_leaf_cake_lpr.jsonl` (36 rows) | 47.07 GB; 8.237 GB | yes |
| total 13,351; about 28 TB (abstract, Table 1, L153) | sums | 12,094+1,160+96+1 = 13,351; 22.554+5.641+0.103+0.047 = 28.35 TB | yes |

## Unchanged numbers

The remaining numbers appear verbatim in v9 with the same occurrence counts. They include the lower-side witnesses, 13,541/190, 42,160/613,228, 5,700 core-hours, 1,075/1,160 at 4 GB, 6 %, 27–28.6 GB determinism, 1,196 = 1,163 + 33, 21 CNF-mismatch runs, 408 h, 1,329,041 clauses, \$225 (H1, L191), f(15)=f(16)=5, Cayley 52/47/57, and the r(109)/r(155) bounds. All were traced in the v8/v9 audits with 0 mismatches.

## Figures

The paper has no `\includegraphics`, so the stale-figure check (step 7) does not apply.

**Mismatches: 0 numerical value mismatches. Untraced: 1 (\$215, critical C2). Wording inconsistency: 1 ("four strata", minor m1).**
