# Changelog: erdos85-drop.7 to erdos85-drop.8

Revision governed by BRIEF amendment R-V8 (2026-10-07), together with R-BRIDGE, R-SIMPLE, R-CERT, the Authorship amendment, R-AUD and R-LINK. This is iteration 8 of `max_iterations: 8`. Inputs: `erdos85-drop.7.review/` (35/44, BLOCK: one critical flag, 4 major, 7 minor, 3 nit), `.7.numeric/` (0 findings), `.7.pending/` (0 markers), `.7.audience/` (6 major unlinked-path hits, all `\repofile` false positives). New refs: `h1_cert_historical96_cake_lpr_receipts.jsonl`, `H1_COVER_AXIOMS_20261006.txt`, and the public guide `research/problems/erdos-85-wip-01/CHECKING.md` with `h1_checker_kit/`.

## Build and gates

- `xelatex main && bibtex main && xelatex main && xelatex main` passes. 0 errors. 0 undefined references or citations. 0 overfull boxes. 4 underfull boxes (status-table cells and the Availability URL line). No `??` in the text layer. The Menlo font-shape warnings are cosmetic.
- 12 pages total. References start at the top of page 11, so the main text is 10 pages (v7: about 9.5). There are no appendices.
- Abstract: 1,765 characters as rendered, and 1,795 characters for a TeX metadata form (macros expanded, `$…$` math kept). Both are under arXiv's 1,920-character limit (v7: about 2,000).
- `scope_lint.py --refs erdos85-drop/refs --proofs <certpilot>/proofs/Proofs`: PASS (34 numbers, 39 Lean names).
- `anvil.lib.numeric_consistency`: pass (312 numbers, 0 findings). `anvil.lib.pending_marker`: pass (0 markers).
- 49 distinct `\repofile` targets, all present in the repository. 40 are on `origin/erdos85/integration`. 9 are only on `origin/erdos85/paper-v6` and land with the merge: `CHECKING.md`, `h1_checker_kit/`, `h1_bank_check_20261006/` and its 3 receipts, `historical96_cake_lpr_receipts.jsonl`, `COMPOSITION_AXIOMS_20261006.txt`, and `H1_COVER_AXIOMS_20261006.txt`.

## Numbers recomputed for this revision

| Paper | Receipt / derivation |
|---|---|
| all 96 historical orbits accepted by cake_lpr | `h1_cert_historical96_cake_lpr_receipts.jsonl`: 96 distinct tags, all `CAKE_LPR_VERIFIED`, `cake_lpr_rc` 0 and `drat_trim_rc` 0 for all 96, checker sha256 `d23c413b…` for all 96 |
| 0.10 TB, largest 2.49 GB (Table 1, §3.2) | sum `lrat_bytes` = 103,469,269,771; max = 2,494,722,547 (derived) |
| same sha256 as the earlier conversion pass | for all 96 tags, the `lrat_sha256` equals the accepted row in `h1_cert_historical96_receipts.jsonl` (0 differ) |
| 50 historical + 30 leaves also accepted by `LRAT.check` | `h1_cert_census_summary.json` `historical_96.LRAT_CHECK_ACCEPTED` 50; `pilot_…std_lrat_check` 30 |
| 23 `native_decide` axioms, no `sorryAx` | `H1_COVER_AXIOMS_20261006.txt`: 23 `…native_decide.ax_*` names plus propext, Classical.choice, Quot.sound |
| 1,157 Graviton + 3 Apple-silicon census rows | census TSV `instance_type`: r8g 459 + r7g.16xl 432 + r6g 263 + r7g.4xl 3 = 1,157; Mac 3 (README "Hosts") |
| about 28 TB | 22.554 + 5.641 + 0.103 + 0.047 = 28.35 TB (derived) |
| about $225 (census + bank re-check) | ≈ $204 (census README) + $20.42 (bank summary). The scope is now stated exactly, since no cost is recorded for the historical cake_lpr pass |
| AMI `ami-05697724475f2e748`, us-east-1, `e85-check`, Requester Pays | `CHECKING.md` steps 1–3 and Files; AMI contents from `h1_checker_kit/ami_setup.sh` (v2cnf, CaDiCaL, cake_lpr, e85-check) |

No number in v8 is untraceable. Two are derived rather than printed in a receipt: 0.10 TB and 2.49 GB, both from the historical cake_lpr JSONL. The "roughly ten times" memory factor, which was weakly traced in v7, is removed.

## v7 review: critical flag

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.7.review (generic, critical flag `close_prior_work_ignored`, blocker B1) | §3 presented the H1 method without its closest precedent (empty-hexagon number) | A new §3 paragraph cites `\citet{heule2024hexagon}` (cube-and-conquer, cake_lpr-checked proof) and `\citet{subercaseaux2024hexagonlean}` (Lean verification of the encoding, joined to the cake_lpr check). Both entries come from the thread `refs.bib`, whose DOIs were resolved per R-V8; none was hand-invented. The paragraph says plainly that their result is **stronger on encoding faithfulness**: their encoding is proved in Lean, while ours links file to formula only through a compiled Lean emitter, with a forward pointer to §3.4. It then names what is distinct here: a whole-stratum Lean reduction to 13,351 formulas, all cake_lpr-checked (about 28 TB); check-then-discard with hash-only receipts and byte-identical regeneration; re-validation of a 22.55 TB archived bank; and a public checker. §1 "What is new" (2) now points to this positioning. The v7 sentence "Our contribution is to run this discipline …", which read as if the pairing itself were new, is gone. |

## v7 review: majors

| Source | Note | Resolution |
|---|---|---|
| .7.review (generic, major M1; R-BRIDGE) | H1 cover theorem called "not part of the cold axiom audit"; Table 2 listed it as open | §2.4 now gives the printed axioms (the three standard ones plus 23 `native_decide` axioms, no `sorryAx`) and links `\repofile{\rp/h1_cert_pilot_20261001/H1_COVER_AXIOMS_20261006.txt}`. The receipt is also linked in §8. Table 2 "H1 reduction" reads "printed axioms: the three standard ones and 23 `native_decide` axioms, no `sorryAx`" / Open: "nothing; not standard-axiom-only". The phrase "not in the cold axiom audit" no longer appears anywhere in the paper. |
| .7.review (generic, major M2; R-BRIDGE/R-V8 §3) | post-table paragraph named only H1 item (i) | Every H1 open-item statement now names both (i) "external checks not admitted into Lean" and (ii) "checked file = Lean formula rests on the compiled emitter". This covers the abstract, §1 "What is not claimed", §3.4, the Table 2 "H1 orbits" row (numbered (i)/(ii), naming `v2cnf`) and the post-table paragraph, which now explains why both items are needed. |
| .7.review (generic, major M3) | headline "formally verified checker" covered 50 orbits checked only by compiled `LRAT.check` with an unverified parser | **Resolved by evidence (R-V8 §1).** All 96 historical orbits were re-checked by cake_lpr, so cake_lpr has checked every one of the 13,351 orbits. The abstract, §1, Table 1 (caption and checker column), §3.4 and Table 2 now say cake_lpr throughout. `LRAT.check` is mentioned once, in the §3.2 historical paragraph, as a redundant cross-check (50 historical + 30 leaves) "not part of the argument". The `lratreplay`/`check_sound` qualification is gone because it is no longer load-bearing. |
| .7.review (generic, major M4) | Lean 4 and Mathlib uncited | `\citep{moura2021lean4}` and `\citep{mathlib2020}` are restored at the first mention of the Lean formalization in §1. The Lean source imports Mathlib and uses its `SimpleGraph`. |

## v7 review: minors and nits

| Source | Note | Resolution |
|---|---|---|
| .7.review (minor m1) | H3 checker unnamed | The cited receipts (`STRATA_AND_SMALL_ORDERS_20260928.md`, `PHASE_B_H1_H3_INVENTORY_20260910.md`) record the two H3 LRAT proofs as checked but do not name the checker, and no other ref does (searched `Q7_H1_H3_SQUEEZE`, `CENSUS.md`, `DRAFT.md`, the direct-edit file). Per R-V8 §5 the paper now says exactly this in §2.3 and in Table 2 ("checker not named in the receipts"), links both receipts, and states that H3 therefore rests equally on the independent paper-and-computation exclusion. |
| .7.review (minor m2) | "None of these steps is a search problem; each has a named Lean interface" overstated | Softened to "None of these steps requires new search, but the H5 premises and the H7 t=0 capstone are substantial formalization work". The "named Lean interface" claim is dropped. |
| .7.review (minor m3) | abstract gap sentence compressed past accuracy | The abstract now names both H1 items and adds "steps for the smaller strata remain open". `native_decide` for the witnesses and for the H1 enumeration is already disclosed earlier in the abstract. |
| .7.review (minor m4) | abstract over 1,920 characters | Trimmed to 1,765 rendered / 1,795 TeX characters. Cuts: the three-way checker split, which is now one clause, and "uniform". |
| .7.review (minor m5) | Table 1 Historical row lacked a size | "0.10 TB, largest 2.49 GB", computed from the historical cake_lpr receipts. |
| .7.review (minor m6) | "roughly ten times the proof's size" weakly traced | **Dropped.** The only refs with memory data (`pilot_h1_81494a_leaf_cake_lpr.jsonl` maxrss) cover cake_lpr, not `LRAT.check`. R-V8 also limits `LRAT.check` to one mention. The surviving sentence makes no comparison: "This bounded memory is what made whole-instance certificates practical." |
| .7.review (minor m7) | f(15)=f(16)=5 is not the refutation of the q=4 analogue | The abstract now reads "its q=4 analogue is false, as Lean exhibits a C4-free 4-regular graph on 16 vertices". §5 names `sixteenRegular`, `sixteenRegular_degree` and `sixteenRegular_common_le_one` (checked by grep in `Erdos85Problem.lean`) and links `\repofile{proofs/Proofs/Erdos85Problem.lean}`. |
| .7.review (nit n1) | BRIEF frontmatter `claim` still says "H1 semantic bridge" | Left for the operator, since the BRIEF is not the reviser's to edit. The paper follows R-BRIDGE/R-V8. |
| .7.review (nit n2) / erdos85-drop.7.audience (6 major) | `\repofile` lines flagged as unlinked paths | False positives, because the detector does not expand `\repofile`. Every flagged path is a live `\repofile` link (49/49 targets exist). No lint-disable directive was added, because that would hide real hits in later passes. |
| .7.review (nit n3) | procedural | No action. |
| erdos85-drop.7.numeric | 0 findings | No action. v8 re-run: pass. |
| erdos85-drop.7.pending | 0 markers | No action. v8 re-run: pass. |

## R-V8 items not raised by the review

| Source | Note | Resolution |
|---|---|---|
| BRIEF R-V8 §4 (public checker) | Availability + one sentence of §3 | §3.4 ends with one sentence: a reader can repeat any part of the H1 check on their own cloud machine with a public image, the published bank proofs and a checker kit. §8 has a new paragraph, "Checking H1 yourself", which gives the AMI `ami-05697724475f2e748` (us-east-1), the `e85-check` tool and its three modes, and states that the 12,094 bank proofs and the checker kit are in a Requester Pays S3 bucket. It links `\repofile{\rp/CHECKING.md}{CHECKING.md}` and `h1_checker_kit/`. R-LINK update: "Not published" now reads "the rest of the certificate storage, the packed H7 certificates, and the artifact volume". The bank is no longer listed as unpublished. The bucket name stays in the guide, not the paper. |
| receipts (found while re-verifying, not raised by the review) | v7 said all 1,160 census rows used the published Linux arm64 binary | The census TSV and README show 1,157 rows on AWS Graviton and 3 on a local Apple-silicon machine, consistent with `CHECKING.md` ("three census orbits were finished on a macOS build"). §3.2 now says so. The checker sha256 `95b64883…` is attributed to the Graviton rows only, because the receipts do not record the Mac rows' cake_lpr build. |
| §3.4 cost sentence | "$225 for the H1 checks" | Scoped to "the census and the bank re-check". The historical cake_lpr pass has no cost receipt. |
| §8 | new receipts | Links added for `historical96_cake_lpr_receipts.jsonl`, `H1_COVER_AXIOMS_20261006.txt` and `COMPOSITION_AXIOMS_20261006.txt`. The older `historical96_receipts.jsonl` is labelled "the earlier conversion pass". |

## Preserved (no regression)

All other v7 content is unchanged in substance: §2.1, §2.2, H5 and H7 in §2.3, §5 apart from the m7 edit, §6 and §7. That covers the Authorship-amendment text, the R-AUD audience discipline (no governance, budget or goal language was added), the epistemic "to our knowledge … at this level of evidence" phrasing, "One drop is compatible with either answer", and A-REG as "a hypothesis with a stated rival". Result A is still never called a theorem, proof or "decided", and cake_lpr is still placed outside Lean ("a HOL4 theorem about its compiled binary, not a Lean kernel check").

## Scope tensions for the next reader

1. **H3 checker.** R-V8 asks the paper to name the H3 checker "from its receipt". No receipt in `refs/` names it, so the paper says it is not recorded and leans on the independent argument. If the operator can find the original H3 check record, one clause can name it.
2. **Precedent details.** The hexagon paragraph states only what BRIEF R-V8 and the bib titles support: 30 points, empty convex hexagon, cube-and-conquer, cake_lpr check, and Lean-verified encoding joined to that check. Web search is off, so no finer claim about their pipeline was made (for example, whether their cube composition is in Lean).
3. **Iteration cap.** This is iteration 8 of 8. A further pass needs an operator sibling or a cap change.
