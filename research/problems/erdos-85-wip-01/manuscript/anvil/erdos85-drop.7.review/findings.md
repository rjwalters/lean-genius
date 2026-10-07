# Findings — erdos85-drop.7

Cross-section observations. The rubric is unchanged from the prior iteration (`anvil-pub-v2` both times), so there is no rubric-transition subsection.

## 1. R-SIMPLE: simplification against the symmetric claim test

**Verdict: achieved, with two small, symmetric miscalibrations and one positioning gap.**

- **Length and structure.** 11 pages total; references start partway down page 10, so the main text is about 9.5 pages (v6: a 23-page document with a 17-page body). No appendices. The section order matches R-SIMPLE items 1–8. There are two tables: Table 1 (the H1 evidence sets) and Table 2 (the single status table). Census-pass history, cost projections, capacity-grid bookkeeping and the replay plan are cut. The dollar figure is one sentence ("about \$225"), and the negative map is down to six bullets with the ledgers linked.
- **Not underclaimed (dim 3).** The cold-reader test passes. The abstract states the drop, the H1 reduction to 13,351 formulas, the all-orbits certificate check with its checkers and its 28 TB scale, and Theorem B, each in its own sentence. §1 "What is new" gives three numbered contributions. §3 presents check-then-discard as a reusable method, as R-SIMPLE asks. Theorem B keeps its residue (defect calculus, NONBIP-CONNECTED with the kernel-dimension identity) and the honest negative map. The one underclaim is R-BRIDGE: the H1 reduction is presented as outside the axiom audit when a receipt now exists (M1). Fixing it strengthens the paper.
- **Not overclaimed (dims 2/9).** Result A is never a theorem. "Not a Lean theorem" sits in the abstract and §1. Nothing is said about Erdős 85 beyond "one drop is compatible with either answer". "To our knowledge … at this level of evidence" stays epistemic. The one overclaim is the headline "formally verified checker" for all 13,351. For 50 orbits the checker is compiled `LRAT.check` with an unverified parser, which §3.2 itself says (M3).
- **What is genuinely interesting survives.** Interesting points that remain: a strict drop at 48→49 that fixes Boza's open $r(42)$; a Lean reduction of the dominant stratum to 13,351 named formulas; the bounded-heap observation that made whole-instance certificates practical; byte-identical regeneration as a substitute for storage; re-validation of a 22.55 TB legacy bank; a Lean-composed cube tree for the one hard orbit; and a uniform one-proposition reduction of the infinite problem, with the $q=4$ analogue failing. The positioning gap (B1/flag) is the main risk to this contribution's reception among formal-methods readers. It is a citation problem, not a substance problem.

## 2. Critical scope rules

| Rule | Status | Evidence |
|---|---|---|
| Result A never theorem/proof/decided | held | `resultA` environment; "Result A is not a theorem of Lean" (§1); scope_lint banned-pattern check PASS |
| "Formally verified checker" only for H1 | held | H3: "checked LRAT proofs"; H7 $t\ge1$: "checked inside Lean by `native_decide`"; H5, H7 $t=0$: "reviewed arguments with independently checked computation". The 50-orbit `LRAT.check` precision issue is M3, within H1 |
| cake_lpr outside Lean | held | "cake_lpr's guarantee is a HOL4 theorem about its compiled binary, not a Lean kernel check" (§3.5); Table 1 caption "All checks ran outside the Lean kernel" |
| `LRAT.check` qualified | held | soundness theorem `Std.Tactic.BVDecide.LRAT.check_sound` named (present in the pinned v4.31.0 source, `Checker.lean:39`); compiled execution and `lratreplay` DIMACS/LRAT parsing "trusted, not verified" (§3.2); "a redundant second check, not part of the trust base" for the 30 leaves (§3.3) |
| Open items stated once, consistent with R-BRIDGE | partly | Table 2 is declared the one list. But (a) the H1-reduction row is stale under R-BRIDGE (M1), and (b) the post-table paragraph omits R-BRIDGE item (ii) (M2) |
| Nothing claimed about Erdős 85 | held | "One drop is compatible with either answer to the problem." |
| A-REG a hypothesis with a rival | held | "a hypothesis with a stated rival"; plane-order rival stated in §5 |
| R-AUD | held | audience scan: 0 governance, 0 private-locator hits; manual read clean; $225 is a cost fact, not a budget |
| R-LINK | held | 44 distinct `\repofile` targets: 39 on `origin/erdos85/integration`, 5 on `erdos85/paper-v6` (bank-check dir and its 3 receipts, `COMPOSITION_AXIOMS_20261006.txt`). Not a defect, per the merge plan. `H1_COVER_AXIOMS_20261006.txt` is committed on `paper-v6` HEAD (`5d2d4bf5802`) but not yet linked (M1). The transcript URL is consistent with R-BRIDGE |
| Authorship amendment | held | author order; joint Sol/Astra sentence; seat-change sentence; neutral Walters credit; room acknowledged, not an author |

## 3. Number verification (recomputed from `refs/`)

| Paper | Receipt / derivation | Status |
|---|---|---|
| 13,351 orbits = 12,094 + 1,160 + 96 + 1 | bank TSV 12,094 distinct tags; census TSV 1,160; historical jsonl 96 (+2 OOM); cube `81494a6ef36d3ec9`; pairwise intersections empty; union 13,351 | verified |
| 13,300 by cake_lpr | 12,094 + 1,160 + 46 | verified |
| 50 by compiled `LRAT.check` | historical jsonl 50 `LRAT_CHECK_ACCEPTED`; census summary `historical_96` | verified |
| 22.55 TB, 6.29 TB compressed, largest 26.5 GB, 8 GB heap, 408 hours | bank TSV sums: 22,554,276,624,018 B; 6,285,686,522,598 B; max 26,521,722,365 B; all heap 8000; 408.47 h | verified |
| one orbit with no producer ledger | `0051c0f06f824a2e`, producer_ledger `none` | verified |
| 21 CNF mismatches on one reclaimed machine | bank summary `CNF_MISMATCH: 21`, note | verified |
| 5.64 TB, largest 36.2 GB, 3,435 / 207 CPU-h | census summary 5,640,561,168,915 B; 36,165,375,193 B; 3,434.7; 207.1 | verified |
| 1,196 records, 1,163 verified, 33 faults, 3 run twice | census summary ledger statuses 1,163 / 30 / 3; determinism pairs 3 | verified |
| 1,075 of 1,160 at 4 GB; none above 16 GB | census TSV heap counts 4000:1075, 8000:72, 12000:1, 16000:12 | verified |
| about 6% checker/solver | 207.1 / 3,434.7 = 6.0% | verified |
| 27–28.6 GB identical pairs | census README determinism | verified |
| 36 leaves, 47.1 GB, largest 8.24 GB, 4 GB heap, cake_lpr `d23c413b…` | pilot jsonl: 47,066,436,918 B; 8,237,398,299 B; heap 4000 ×36; checker sha prefix d23c413b ×36 | verified |
| 30 smaller up to 2.42 GB | 30th-smallest leaf 2,419,876,486 B; 31st-smallest 2,847,830,901 B | verified |
| sha256 for only 30 leaves | the pilot cake_lpr jsonl in `refs/` has no proof sha256 at all; the 30 come from the `LRAT.check` leaf receipts (verified by the v6 reviewer, not in thread refs) | consistent, not directly traceable in `refs/` |
| depth at most 8 | `cube-tree-check.json` `max_depth: 8`, 36 leaves, 35 splits | verified |
| about 28 TB | 22.554 + 5.641 + 0.103 (historical) + 0.047 (leaves) = 28.35 TB | verified (derived) |
| about \$225 | ≈ \$204 (census README) + \$20.42 (bank summary) | verified (derived) |
| 13,541 representatives, 190 removed | `PHASE_B_H1_H3_INVENTORY_20260910.md` "13,541-row raw compact inventory … 13,351-row capacity-filtered universe"; 13,541 − 13,351 = 190 | verified |
| 42,160 vars / 613,228 clauses | `CENSUS.md` | verified |
| 1,161 verdict-only, about 5,700 core-hours | `CENSUS_TIMING_20260928.md` "about 5,716 core-hours" | verified |
| H3 29,500 vars / 1,328,183 clauses; H7 1,329,041 clauses; 2,278,608 / 445,699; 43/15/28; 13/12/92 | H7_POSITIVE_TRIPLE…, H7_CLOSURE, H5 ledger README | verified (scope_lint PASS) |
| ten graphs (Afzaly–McKay) | BOZA48 receipt "non-isomorphic to all 10 Afzaly--McKay archive graphs" | verified |
| 20 solver attempts; 52/47/57 Cayley groups; thousand $q=4$ models; row 175 | DRAFT.md and the linked ledgers only | traceable to the linked ledgers; carried from the AUDITED v4/v5 text |
| roughly ten times the proof size | BRIEF R-CERT and the operator's direct-edit file only | weakly traced (m6) |
| 23 `native_decide` axioms (cover theorem; not yet in paper) | `H1_COVER_AXIOMS_20261006.txt`: 23 distinct `…native_decide.ax_*` names plus 3 standard | for M1 |

No untraceable number was found. Two are weakly traced (the ten-times memory factor, and the 30-leaf sha256 claim relative to the thread's `refs/`), and both are disclosed or consistent.

## 4. Prior-review item disposition

- B1 / critical flag: resolved by evidence (bank re-check).
- M1, M2: resolved (§3.2, §3.3).
- M3: moot (the 34 slots lie in the verified bank).
- m2, m3, m4, m5, m7, n4: resolved.
- m1 (title): declined by BRIEF and now closer to accurate.
- m6: partly (`check_sound` named; no bib entry; Lean 4 itself now uncited, see M4).
- n3: resolved by R-BRIDGE.
