# Findings — erdos85-drop.6

Cross-section observations for the reviser and the operator. The prior review (`erdos85-drop.5.review/`) was scored against the same rubric (`anvil-pub-v2`), so there is no rubric-version-transition subsection.

## 1. Receipt recomputation of every new H1-certification number

The `refs/` receipts were recomputed in Python, together with the two public pilot receipts that have no `refs/` copy (`h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_solves.jsonl` and `..._std_lrat_check.jsonl`, read on the certpilot worktree, branch `erdos85/paper-v6`).

| Paper statement (location) | Receipt | Recomputed | Status |
|---|---|---|---|
| 1,160 rows certified (S1, S4.5, T5) | TSV, summary.json | 1,160 rows, all CERTIFIED, 1,160 distinct ids and CNF hashes; id set equals the census's 1,160 UNSAT_CROSSCHECKED rows; 0 overlap with the historical 96; hardest row absent | OK |
| 5.64 TB, largest proof 36.2 GB | TSV | 5,640,561,168,915 B; max 36,165,375,193 B (h1_3852b751..., Mac) | OK |
| 3,435 solver / 207 checker CPU-h; "about 6%" | TSV, summary | 3,434.73 / 207.09; 6.03% | OK |
| 1,157 Graviton (r6g/r7g/r8g) + 3 Mac, Mac includes largest proof | TSV | 459 r8g.16xl, 432 r7g.16xl, 263 r6g.16xl, 3 r7g.4xl; 3 Mac including the max row | OK |
| 1,196 ledgers = 1,163 + 30 + 3 | summary.json | same | OK |
| three rows certified twice, byte-identical, 27 to 28.6 GB | TSV, README | 27.17 / 28.08 / 28.59 GB, identical | OK |
| 4 GB for 1,075 rows, no row above 16 GB | TSV heap_mb | 4,000x1,075; 8,000x72; 12,000x1; 16,000x12 (assigned heaps) | OK |
| about 1.6 GB per CaDiCaL CPU-hour | TSV | 1.64 | OK |
| 6.3 GB per CPU-hour on the leaves | leaf_solves.jsonl (public, not in refs/) | 47.066 GB / 7.421 h = 6.34 | OK (receipt linked, not in refs/) |
| 36/36 leaves cake_lpr; 30 also LRAT.check; six largest cake_lpr only | pilot jsonls, summary | 36 / 30 (max accepted 2.42 GB); the six above it run 2.85 to 8.24 GB | OK |
| 96 historical: 50 LRAT.check, 46 cake_lpr, two OOM first attempts re-checked | historical96 jsonl | 98 lines 50/46/2 OOM (both later CAKE_LPR_VERIFIED); 96 tags; all drat_trim_rc 0; 95 p0 + 1 p1 | OK |
| composition lemma axioms propext, Quot.sound | COMPOSITION_AXIOMS | four statements [propext, Quot.sound] | OK |
| about $204 incl. 10% margin; seven spot reclaims | README | same | OK |
| "each cube CNF hash-checked against the tree" | leaf_solves + tree results.json | 31 explicit cube_sha_ok true, 5 lack the field; all 36 match the (unpublished) tree results.json | OK (changelog loose, nit n1) |
| "each receipt keeps the proof's sha256 and length" (T5 caption) | all receipt sets | census and historical yes; leaves: sha256 only for the 30 LRAT.check leaves | Overstated (M2) |
| profile split 283/346/388/198/42 | census TSV, historical | 187+95+1 = 283; 345+1 = 346; rest equal | OK |
| S4.6 projection: 12,102 rows, 5 to 6 GB/h, 2,704 h -> 14.9 TB, 60 to 130 GB | CERT_BANK_STATS, CENSUS_TIMING | as stated | OK |
| 1,254 certified capacity slots = 1,158 + 96 (T4) | CENSUS.md | 1,158 + 96; 1,191 fresh = 1,157 + 34 | OK |

No number in the new material lacks a receipt. The scope problem (B1) is not a numerical error. Every number is right; the sentences that put "every" and "whole stratum" around them are not.

## 2. The H1 scope problem in detail (critical flag 1)

The thread's own receipts give three nested sets:

1. **The capacity-filtered universe: 13,351 rows.** This is what "the full 13,351-slot closure" means in `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`; the paper cites it at L232.
2. **Rows screened out of Phase B because a 2026-08 bank object exists: 11,954 + 140 = 12,094** (`PHASE_B_H1_H3_INVENTORY_20260910.md`). The bank holds 12,102 UNSAT rows; the replay plan targeted 12,019 "historical ready" inputs. Verification is producer-side (ledgers record exit 20 and trim verification, i.e. drat-trim at production). The inventory says "uploaded certificates were not downloaded or kernel-checked in this pass".
3. **The frozen Phase B set: 1,257 = 1,161 residual + 96 historical.** This is exactly the set the October run checked; the README says "Every H1 residual root".

The paper's sentences claim set 1 while the evidence covers set 3:
- "consists of 1,257 SAT instances, and every one of them" (Abstract)
- "Every H1 instance now carries a checked certificate" (S4.5)
- "the whole stratum was certificate-checked in one run" (S6)
- "All of H1 | 1,257" (Table 5)

The 96 historical rows have the same evidence class as set 2, and v6 re-checks them. Having done so, the paper cannot treat set 2 as already verified.

**What v5 said and v6 dropped.** v5 S6 said "The bank of 12,019 historical ready certificate inputs for the H1 rows is inventoried (objects and metadata, not yet validated payload by payload)", and v5 had a matching Table 4 row. v6 removed the row as "obsolete" and calls the bank-replay plan "superseded" (L362). Neither is true: the October run did not replay the bank.

**The BRIEF claim.** The frontmatter claim ("Every SAT instance behind the 48-to-49 drop now has an unsatisfiability certificate accepted by a formally verified checker") exceeds the receipts in three ways: the bank, H3 (whose LRAT checks the paper does not call verified) and H5 (no SAT certificates). The operator should amend it.

**Minimal faithful rewrite (no new numbers).** "H1 is closed over a 13,351-slot capacity universe. All but 1,257 slots are covered by certificates from the 2026-08 campaign, verified by drat-trim when they were produced; the remaining 1,257 (1,161 residual roots and 96 historical rows) were each certificate-checked in October 2026 by .... Re-validating the 2026-08 bank by a verified checker is open." Add the bank to every gap list, restore the Table 4 bank row, and say whether the 34 outside slots are needed (`PAUSE_HANDOFF_20260927.md`: "The capacity-grid framing (1,288 gap slots) additionally needs the 34 outside-frozen slots").

## 3. Checker trust: cake_lpr versus compiled LRAT.check (dispatcher item 3)

| | cake_lpr | compiled LRAT.check (via lratreplay) | H7 LRAT.check by native_decide |
|---|---|---|---|
| Algorithm soundness | HOL4 theorem | Lean `Std.Tactic.BVDecide.LRAT.check_sound` (present in v4.31.0) | same |
| Execution | CakeML-verified machine code | Lean compiler and runtime (trusted) | Lean compiler (Lean.ofReduceBool) |
| DIMACS / proof parsing | inside the verified theorem | `Proofs.Erdos85LratRuntime` front end, unverified | the CNF is a Lean term; the proof is parsed in Lean inside the theorem |
| Result recorded in Lean | no | no | yes |
| Sole checker for | 1,160 census rows, 46 historical, 6 leaves | 50 historical | 13 H7 representatives |

The body's "whose soundness is a Lean theorem but whose execution trusts the compiler" is accurate as far as it goes. It omits the unverified parsing front end, and it puts trust in LRAT.check for 30 leaves that cake_lpr also accepted (redundancy, not trust). The abstract's "formally verified checker" for the 50 is defensible under the standard bv_decide reading, but needs a one-clause qualifier. This is a major comment (M1), not a flag.

## 4. The .5.operator flags and audit nits

All three flags and both audit nits are resolved in the text (see verdict.md). The authorship amendment is implemented faithfully:
- author order Fable, Sol, Astra, Opus, Walters;
- the joint Sol/Astra sentence is verbatim;
- the seat-change sentence is present;
- Walters's credit is neutral;
- the room infrastructure is acknowledged, not an author;
- the old "human operator ... not an author" sentence is gone.

## 5. Disclosure diff, v5 to v6

Every v5 disclosure about H3, H5, H7, the witnesses and Theorem B is retained. The one weakened disclosure is the certificate bank (S2 above). The added disclosures are:
- the external checks are not in Lean;
- the composition lemma's leaves are hypotheses;
- certificates say nothing about the encoding;
- the 34 slots are verdict-only;
- cake_lpr's exit-0 trap;
- reproduction pins the exact binary.

## 6. Gates and tools

| Tool | Result |
|---|---|
| render gate (_gate.json) | pass: 23 pp, 0 overfull boxes above 5 pt, 0 placeholders |
| numeric_consistency | 935 numbers, 1 claim, 0 findings |
| pending_marker | 0 markers |
| audience_check | 0 governance, 0 private locator, 14 unlinked-path hits, all \repofile false positives |
| evidence_drift | CLEAN |
| evidence_check (staged scoring.md) | 9 dimensions, 0 findings |
| scope_lint.py --proofs certpilot | PASS (58 numbers, 57 Lean names) |
| R-LINK | 71 distinct paths; 70 on origin/erdos85/integration; COMPOSITION_AXIOMS on erdos85/paper-v6 (lands with the merge); README and transcript URLs HTTP 200 |
| citations | 14/14 resolve; BibTeX 0 warnings; pdftotext 0 "??" |
