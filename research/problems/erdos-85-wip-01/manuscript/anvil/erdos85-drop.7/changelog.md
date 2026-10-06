# Changelog: erdos85-drop.6 to erdos85-drop.7

Revision governed by BRIEF amendment R-SIMPLE (2026-10-06). This is a restructuring and simplification, not a line edit. Inputs consumed: `erdos85-drop.6.review/` (34/44, BLOCK, one critical flag, 3 major, 7 minor, 4 nit), `.6.numeric/` (0 findings), `.6.pending/` (0 markers), `.6.audience/` (14 major unlinked-path hits, all `\repofile` false positives), and the new refs `H1_BANK_CHECK_README_20261006.md`, `h1_bank_check_summary.json`, `h1_bank_check_receipts.tsv`.

## Build and gates

- `xelatex main && bibtex main && xelatex main && xelatex main`: 0 errors, 0 undefined references or citations, 0 overfull boxes, 5 underfull boxes (status-table cells), 0 `??` in the text layer. Menlo font-shape warnings are cosmetic.
- 11 pages total. References start 48% down page 10, so the main text is about 9.5 pages. There are no appendices. v6 had 23 pages with a 17-page body.
- `scope_lint.py --proofs <certpilot>/proofs/Proofs`: PASS (32 numbers, 37 Lean names).
- All 45 distinct `\repofile` paths exist. 41 are on `origin/erdos85/integration`. 4 are only on `erdos85/paper-v6` HEAD and land with the merge: `h1_bank_check_20261006/` and its three receipts, plus `h1_cert_pilot_20261001/COMPOSITION_AXIOMS_20261006.txt`.

## New structure (R-SIMPLE items 1 to 8)

| § | Title | Approx. pages | R-SIMPLE item |
|---|---|---|---|
| Abstract | two results, gaps named once briefly | 0.5 | |
| 1 | Introduction (Result A and Theorem B stated, what is new, what is not claimed) | 0.75 | 1 |
| 2 | The drop at 48 to 49 (lower sides, case split, H3/H5/H7, H1 and its 13,351 orbits) | 2.1 | 2 |
| 3 | How H1 was checked (check-then-discard, four evidence sets with Table 1, hardest orbit, what the check establishes) | 2.3 | 3 |
| 4 | Status (Table 2, the single list of open items) | 0.9 | 4 |
| 5 | Theorem B and the residue beneath A-REG (reduction, defect residue, NONBIP-CONNECTED, evidence including f(15)=f(16)=5) | 1.3 | 5 |
| 6 | What does not close A-REG (condensed negative map, six items, ledgers linked) | 0.75 | 6 |
| 7 | Collaboration and methods (contributions, seats, cold-audit rule, two lessons) | 0.55 | 7 |
| 8 | Availability (R-LINK) | 0.75 | 8 |

## v6 review: critical flag and majors

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.6.review (generic, critical flag `scope_overclaim_h1_certificate_check`, blocker B1) | "H1 is 1,257 instances" omitted the ~12,000 orbits resting on the unchecked 2026-08 bank | **Resolved by evidence, not wording.** The bank re-check (refs `H1_BANK_CHECK_README_20261006.md`, summary, TSV) verified 12,094/12,094 with cake_lpr. Recomputed from the TSV: 12,094 distinct tags, all VERIFIED; 22,554,276,624,018 LRAT bytes; 6,285,686,522,598 gz bytes; max 26,521,722,365; every heap 8,000 MB; 408.47 summed check-hours. The bank, census (1,160), historical (96) and cube orbit sets are pairwise disjoint, and their union is exactly 13,351 tags. H1 is now stated throughout as 13,351 capacity orbits, with a paragraph on what an orbit is and why 13,351 suffice (§2.4). Table 1 gives the four disjoint sets. The bank-row restoration and the "superseded"/"not run" fix are moot: the bank was run. |
| same (B1 sub-item: the 34 outside slots) | Do the 34 verdict-only outside slots matter? | Checked against `h1-gap1288-audit.json`. The 1,288 gap ids decompose as 34 in the bank set, 1,157 in the census set, 96 historical and 1 cube orbit. So the 34 "outside" slots are among the 12,094 bank orbits now verified by cake_lpr. They are no longer verdict-only. The capacity-grid bookkeeping is cut per R-SIMPLE. |
| same (M1 / R-SIMPLE (a)) | compiled `LRAT.check` trust statement incomplete, and wrong direction for the leaves | §3.2 "The historical certificates" now names the `lratreplay` executable (linked `Erdos85LratRuntime.lean`). It states that the algorithm is proved sound (`Std.Tactic.BVDecide.LRAT.check_sound`), while compiled execution and the DIMACS/LRAT parsing front end are trusted, not verified. It compares this to the `native_decide` trust and notes that cake_lpr's theorem covers parsing. §3.3 says that for the 30 cube leaves `LRAT.check` is "a redundant second check, not part of the trust base". The abstract carries the qualifier "whose algorithm is proved sound in Lean and which we ran compiled". The checker is named one way throughout (n4). |
| same (M2 / R-SIMPLE (b), (c)) | hardest-row statements did not match receipts | §3.3: the leaves were "re-solved ... by the macOS build of CaDiCaL 3.0.1 ... written to files and checked afterwards by a separate cake_lpr build (sha256 `d23c413b…`), with a 4 GB heap". Verified against `pilot_h1_81494a_leaf_cake_lpr.jsonl`: 36/36 `d23c413b`, all heap 4,000 MB, 47,066,436,918 bytes in total, largest 8,237,398,299. "The leaf receipts record each proof's length, but a proof sha256 only for those 30 leaves." The "checked the same way" phrasing and the v6 Table 5 caption are gone. |
| same (M3) | the 34 outside slots | See the B1 sub-item above. |
| R-SIMPLE (d) / m7 | "1,160 instances of a two-solver census" excluded the cube row | That phrasing is gone. The census set is defined as "Of the 1,161 orbits with no August certificate, the 1,160 other than the hardest" (§3.2), and the hardest orbit is its own row in Table 1. |
| R-SIMPLE (e) / m6 | cite the Lean LRAT checker; keep `heule2018schur`, `tan2021cakelpr` | Both entries are kept. There is no bib entry for Lean's LRAT checker, and none is invented (web search off). It is identified by its standard-library theorem name `Std.Tactic.BVDecide.LRAT.check_sound` under the existing `moura2021lean4` context. That name is wrapped in a `\stdlean` macro, because scope_lint checks only `proofs/Proofs` declarations; the v6 reviewer confirmed the theorem exists in the pinned v4.31.0 toolchain. Whether the Pythagorean/Schur citations support the check-then-discard attribution is left to `paper-audit`, as v6 recommended. |

## v6 review: minors and nits

| Source | Note | Resolution |
|---|---|---|
| .6.review (minor m1) | Title "Certificate-Checked Drop" is shorthand for H5 and H7 t=0 | Declined: the title is fixed by the BRIEF frontmatter. With all of H1 now certificate-checked the shorthand is closer. The Result A statement and Table 2 say exactly which strata rest on reviewed arguments. |
| .6.review (minor m2) | §4.6 counterfactual "splitting would multiply bytes" overgeneralized | Dropped, together with the whole "why the whole-instance route sufficed" projection material (R-SIMPLE cut). One sentence remains: bounded-heap streaming "is what made whole-instance certificates practical". |
| .6.review (minor m3) | abstract key sentence hard to parse | Rewritten as three short sentences: 13,300 by cake_lpr; 50 by Lean's LRAT checker; the hardest by 36 cubes plus the Lean lemma. |
| .6.review (minor m4) | 459-word Result A paragraph in §1 | §1 now states Result A in four lines. Census history is cut to one sentence in §2.4. |
| .6.review (minor m5) | five-gap list repeated five times | The open items are listed once, in Table 2 and the paragraph after it. The abstract carries one compressed sentence, and every other mention points to Table 2. |
| .6.review (nit n1) | changelog `cube_sha_ok` description | The paper keeps "each leaf's CNF hash-checked against the tree", which the v6 reviewer verified for all 36. No receipt-field claim is made. |
| .6.review (nit n2) / erdos85-drop.6.audience (14 major) | `\repofile` lines flagged as unlinked paths | False positives, because the detector does not expand `\repofile`. Every path in §8 is a `\repofile` link. No change needed. |
| .6.review (nit n3) | BRIEF says transcript not published; paper links it | Kept the transcript URL in §7 (HTTP 200 per the v6 reviewer). The BRIEF line remains for the operator to reconcile. |
| .6.review (nit n4) | three names for the second checker | One name throughout: "Lean's `LRAT.check`" / "the LRAT checker of Lean's standard library", with the namespace given once. |
| erdos85-drop.6.numeric | 0 findings | No action. |
| erdos85-drop.6.pending | 0 markers | No action. |

## Earlier fixes carried forward

- R-CERT operator_defect (a): §2.1 says the audit output prints only the per-declaration `native_decide` axiom names, and that identifying them with `Lean.ofReduceBool` is a statement about Lean's implementation.
- R-CERT (c): the abstract discloses `native_decide` for the witnesses.
- R-CERT operator_defect (b): Appendix B and its "thirteen input hashes" sentence are cut entirely.
- Authorship amendment: author order, the joint Sol/Astra sentence, the seat-change sentence, Walters's neutral credit, and the room acknowledged but not an author (§7).

## What was cut, and where it went

| Cut material (v6 location) | Where it lives now |
|---|---|
| Verdict-only census passes table and narrative, the 1,412 preparation receipts, spot reclaims, the $235 census cost (v6 §4.2, Table 3) | One sentence in §2.4, linked to `CENSUS.md`; core-hours in `CENSUS_TIMING_20260928.md` (linked in §8) |
| Capacity-grid gap bookkeeping: 1,288 slots, 34 outside, auditor's 1,191/96/1 and "97 open" (v6 §4.2, Table 4 row) | Cut. Moot, because all 13,351 orbits are verified. `CENSUS.md` and the gap audit remain in the census directory. |
| Projection, "why the whole-instance route sufficed", the 14.9 TB estimate, the replay plan and 48 GiB gate (v6 §4.6, §7 bullets) | One sentence in §3.1. `CERT_BANK_STATS` and the replay-plan links are dropped from the paper. |
| Overlapping tables: axioms (v6 Table 1), strata inputs (Table 2), evidence levels (Table 4), Oct check (Table 5) | Replaced by Table 1 (H1 evidence sets, data) and Table 2 (the single status table). Axiom facts are now in the §2.1 prose and Table 2. |
| Two Lean consumers / cube-grid accounting (392 cubes, 406 jobs), H5 inventory roots 3×43=129 (v6 §3.2, §4.2) | Cut. Linked in `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md` and `Q7_H5_H7_SQUEEZE_20260910.md` (§8). |
| Review numbers 2037/2032/2062/2063/2065/1573/1574/2091 | Cut from the text (R-AUD hygiene). They remain in the linked H5 ledger and H7 closure files. |
| Separate Related work section (v6 §2) | Boza / Afzaly–McKay / Erdős record in §1 "What is new" and §2.1. SAT, LRAT, cake_lpr and check-then-discard lineage in the §3 opening. No citation removed. |
| Interpretation section (v6 §6) | Folded into §1 (what is and is not claimed) and §4. |
| Appendix A negative map (nine bullets, order-64 and plane-order paragraphs) | §6, six bullets, with `FINAL_PROOF_OUTLINE.md` and `CUTS_LEDGER_DRAFT.md` linked for the rest |
| Appendix B (verification asymmetry, adversarial diversity, structure–compute exchange rate, methods list) | §7 keeps the seat and cold-audit methods and two lessons (the order-64 encoding error; "silence is not success", now with the cake_lpr exit-0 trap). The rest is cut. |

## New facts added (each traced)

- **H1 reduction in Lean.** `orderFortyNineStratumExcluded_one_of_capacityInventory_checked` (`Erdos85OneHighV2CapacityCover.lean`, on integration since commit `ca91cdc85da`, 2026-08-15) proves that `OneHighFamilyV2CheckedUnsat` for each of the 13,351 capacity-inventory tables implies `OrderFortyNineStratumExcluded 1`. It goes through the proved cover `oneHighRawV2OrbitCover_capacityInventory` and the count `oneHighCapacityInventory_total_length` (13,351 of 13,541). The cover's finite checks use `native_decide`. The paper says this, and says the statement was not in the cold audit. See the scope tension below.
- **Orbit definition.** From `Erdos85OneHighV2ProfileSymmetry.lean`, `Erdos85OneHighV2OrbitExclusion.lean` and `Erdos85OneHighV2CapacityInventory.lean`: profile-preserving matching-commuting permutations act on miss tables, and every H1 graph can be labelled so that its table is a stored representative. The capacity inequality removes 190 of the 13,541 representatives.
- **Emitter identity.** `v2cnf emit` prints `oneHighFamilyV2Clauses profile table` (source `Erdos85OneHighV2CnfEmit.lean` lines 111 and 143), so the external file is the compiled print of the Lean term.
- **Derived totals.** 13,300 = 12,094 + 1,160 + 46 (cake_lpr whole-instance). About 28 TB = 22.554 + 5.641 + 0.047 (leaves) + 0.103 (historical LRAT bytes from `h1_cert_historical96_receipts.jsonl`) = 28.35 TB. About $225 = about $204 (census README) + $20.42 (bank summary). The 1,075/1,160 4 GB heaps were recounted from the census TSV.

## Scope tensions for the operator

1. **"H1 semantic bridge (row-to-stratum assembly) is open"** (BRIEF R-CERT, `PAUSE_HANDOFF`, `STRATA_AND_SMALL_ORDERS`, v6). The Lean source has had the row-to-stratum assembly over the 13,351 orbit formulas since 2026-08-15 (above). What is actually open for H1 is (i) admitting the external checks as `OneHighFamilyV2CheckedUnsat` proofs, and (ii) the identity between the externally checked DIMACS file and the Lean term, which rests on the compiled emitter. The cover also depends on `native_decide`, and its axioms were never printed in a cold audit. v7 keeps the name "the H1 bridge" for (i) and (ii) in Table 2 and states the Lean theorem with its caveats. It does not claim the assembly is axiom-audited. The operator may want the BRIEF's gap wording updated and a `#print axioms` receipt for `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`. That needs a Lean build, which was not run here.
2. **BRIEF number-trace rule vs R-SIMPLE.** The early rule says "no new numbers". v7's new numbers come from the R-SIMPLE receipts, from Lean source declarations (13,541, 13,351, 190) or from arithmetic on receipts (13,300, about 28 TB, about $225). Each is listed above.
3. **"About ten times the proof size"** for `LRAT.check` memory traces only to BRIEF R-CERT and the operator's `MAIN_TEX_20261006_H1_CERT_DIRECT_EDITS.tex` ("23.5 GB for a 2.3 GB proof"). No standalone receipt exists. It is kept as "in our pilot, roughly ten times".
