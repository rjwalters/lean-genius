# Numerical audit: erdos85-drop.9

**Method.** v9 changes relative to v8 are confined to the abstract, Result A, §1 "What is not claimed", §2.3 H3, the §2.4 `native_decide` parenthetical, the §3 opening comparison, §3.2 (historical paragraph, cost sentence moved), Table 2 H3 row, the post-table paragraph, §8, three `refs.bib` capitalizations, and the title (diff of `erdos85-drop.8/main.tex` vs `erdos85-drop.9/main.tex`). Every number in the new or edited text was checked against its receipt below. Numbers in unchanged text were fully traced in `erdos85-drop.8.audit/numerical-audit.md`; the H1 core totals were recomputed again this run from the per-row receipts. The deterministic `erdos85-drop.9.numeric/` sibling (328 numbers, 0 findings) and `scope_lint.py` (34 numbers, 40 Lean names: PASS against `erdos85-certpilot/proofs/Proofs`) agree.

## New or edited numbers (v9)

| Text claim (main.tex line) | Source | Source value | Match | Notes |
|---|---|---|---|---|
| H3: two cells; $t=1$ one low vertex adjacent to all three highs; $t=0$ three pair vertices spanning a matching with $b\in\{0,1\}$ edges (L110) | `Q7_H3_PROFILE_EXCLUSION_20260910.md` ¶3–4 | triple profile: one triple-support low vertex; pair profile: three pair-support vertices, "a matching with b=0 or b=1 edges" | yes | |
| 3,337 induced cases for $t=1$ (L110) | same, table row "Triple" | "3,337 induced U/R cases" | yes | |
| 972 ($b=0$) and 3,600 ($b=1$) combinations of normalized core and host choice (L110) | same, rows "Pair, b=0/1" | 36×27 = 972; 75×48 = 3,600 | yes | |
| each enumeration passed independent review; two $t=0$ searches replayed from unchanged source with no time limit, exact agreement (L110) | same, ¶ after table | "Every listed review resolved PASS. The full-completion reviews used unchanged-source, no-deadline replays and obtained exact agreement" | yes | full-completion reviews 1679/1681 are the two pair ($t=0$) branches |
| "no SAT verdict or LRAT proof exists for either cell formula" (L110) | `H3_EVIDENCE_AUDIT_20261007.md` Verdict ¶1 | verbatim substance | yes | |
| Lean: `threeHighCanonicalGraphCover_all`, `orderFortyNineStratumExcluded_three_of_representativeExclusions` in `Erdos85OrderFortyNineThreeHighOneFiber.lean` (L110) | `proofs/Proofs/Erdos85OrderFortyNineThreeHighOneFiber.lean` L530, L537 | cover for `blocks ≤ 1`; reduction takes `∀ index ≤ 1, ThreeHighCanonicalRepresentativeExcluded index` | yes | grep only, no build. The H3 evidence audit names the module `Erdos85ThreeHighOneFiber.lean`; the paper's longer name is the one that exists. |
| Table 2 H3 row: "two cell-exclusion premises" (L205) | same theorem | one hypothesis quantified over the two indices | yes | |
| abstract ≈ ≤1,900 chars (R-V8 §5) | `pdftotext` of fixpoint PDF | 1,830 rendered characters | yes | under arXiv's 1,920 |
| "about \$225" (L175, moved from §3.4) | census README ≈ \$204; `h1_bank_check_summary.json` `cloud_spend_usd_estimate` 20.42 | ≈ 224.42 | yes | scope ("census and the bank re-check") unchanged |
| 13,351 count `oneHighCapacityInventory_total_length`, "by `native_decide`" (L122) | v8 audit N6 | proved by `native_decide`; not in the cover theorem's axiom list | yes | v8 nit N6 applied |
| title / 12 pp / main text 10 pp | fixpoint build | 12 pages; "References" on p. 11 | yes | |

## H1 core totals (recomputed this run)

| Text claim | Source | Recomputed | Match |
|---|---|---|---|
| 12,094 bank orbits; 22.55 TB; largest 26.5 GB (Tab 1, L171) | `h1_bank_check_receipts.tsv` (12,094 rows) | Σ`lrat_bytes` 22.554 TB; max 26.52 GB | yes |
| 6.29 TB compressed; 408 h; 21 CNF-mismatch runs; 1 orbit without producer ledger (L171) | `h1_bank_check_summary.json` | 6.286 TB; 408.5; `CNF_MISMATCH` 21; `0051c0f06f824a2e` | yes |
| 1,160 census; 5.64 TB; largest 36.2 GB; 3,435 / 207 CPU-h; 1,196 records = 1,163 verified + 33 faults (L162, L173) | `h1_cert_census_summary.json`; TSV 1,160 rows | 5.6406 TB; 36.17 GB; 3,434.7 / 207.1; 1,163 + 30 + 3 | yes |
| historical 96; 0.10 TB; largest 2.49 GB; all cake_lpr (L163, L175) | `h1_cert_historical96_cake_lpr_receipts.jsonl` (96 rows) | Σ 0.1035 TB; max 2.495 GB; all `CAKE_LPR_VERIFIED` | yes |
| hardest orbit: 36 leaves, 47.1 GB, largest 8.24 GB (Tab 1, L181) | `pilot_h1_81494a_leaf_cake_lpr.jsonl` (36 rows) | Σ 47.07 GB; max 8.237 GB | yes |
| total 13,351; about 28 TB (Tab 1, abstract) | sums above | 12,094+1,160+96+1 = 13,351; 22.554+5.641+0.103+0.047 = 28.35 TB | yes |

## Unchanged numbers

All other numbers (lower-side witnesses, 13,541/190, 42,160/613,228, 5,700 core-hours, 1,075/1,160 at 4 GB, 6 % checker cost, 27–28.6 GB determinism pairs, 30 leaves with sha256 up to 2.42 GB, H5 49 masks/13 classes/12/92 branches, H7 fourteen/thirteen representatives, 1,329,041 clauses, 43/15/28 classes, 2,278,608/445,699, f(15)=f(16)=5, Cayley 52/47/57 groups, r(109)/r(155) bounds) are byte-identical in v9 and were traced in `erdos85-drop.8.audit/numerical-audit.md` with 0 mismatches.

## Figures

No `\includegraphics`; the stale-figure check (step 7) does not apply.

**Mismatches: 0. Untraced numbers: 0.**
