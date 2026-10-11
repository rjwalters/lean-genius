# Verdict — erdos85-drop.10

**Total: 37 / 44** (prior iteration `erdos85-drop.9.review/`: 39 / 44)

**Decision: `advance: true`.** The total clears the 35-point threshold, and no critical flag is set. The pending-marker gate passed (0 markers), so `ready: true`.

This is iteration 10 of `max_iterations: 8`, an operator-override status pass (`metadata.operator_override: true`, `direct_edit: true`). Its only authority is `erdos85-drop.9.operator/`, an agent-transcribed record of operator chat instructions. It is not a human review and raises no flags. The three majors below are small direct edits, one of them to `BRIEF.md`. They should land before the tag and Zenodo step, not in another lifecycle iteration.

## The overclaiming check (the review's main risk)

Every mention of the upper side was read against the stated standard: a Lean theorem conditional on two explicit UNSAT hypotheses supported by external cake_lpr checks, and never an unconditional Lean theorem. The mentions checked are the abstract, Result A, §1 "What is new" and "What is not claimed", §2.2, §2.3, §3, §3.4, Table 2, the post-table paragraph and §7. **The paper meets the standard everywhere.**

- **Abstract [L66].** "The result is a Lean theorem conditional on two explicit unsatisfiability hypotheses, supported by the external checks but not admitted into Lean; each checked file is tied to its Lean formula by a compiled emitter, not a kernel proof."
- **Result A [L78].** It names the theorem and says its "only hypotheses are $h_{\mathrm{H1}}$ ... and $h_{\mathrm{H7}}$".
- **"What is not claimed" [L87].** It opens "Result A is not an unconditional theorem of Lean".
- **Table 2 [L226].** It lists "the two hypotheses" as open.
- **Source check.** The source at the pinned commit agrees. `not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence` takes exactly `hOne`, `depth` and `hSeven`. Its docstring says "this is not an unconditional Lean proof".
- **No promotion of external checks.** No sentence calls cake_lpr evidence a kernel check. No sentence says H1 or H7 is "proved in Lean". Nothing is claimed about Erdős 85.

**Residual risk (M3, process).** The BRIEF still says "Never call Result A a theorem", and its `claim` says "not a Lean theorem ... H3 and H5 premises ... open in Lean". v10's "The result is a Lean theorem conditional on ..." is accurate, but it conflicts with the letter of an unamended hard rule. The operator-agreed wording was "Lean-verified reduction conditional on explicitly stated UNSAT evidence". Either the operator amends the BRIEF (R-V10), or the abstract sentence is reworded so that the theorem is the implication (see Top fixes). I do not raise this as a critical flag, because the paper's substance meets the dispatch's stated standard.

## Number reconciliation (all consistent)

| Number in paper | Source | Match |
|---|---|---|
| 28 covers, 377,776 leaves, 377,804 formulas | `summary.json`: 28 cubes, leaves 377,776, missing 0; 28 + 377,776 = 377,804 | yes |
| 377,775 leaves + 257 split formulas verified | totals: `leaf:CERTIFIED` 377,775, `split:CERTIFIED` 257; `split_leaves` 1 | yes |
| 4,269 solver / 706 checker CPU-h, ~20.2 TB (leaf + split, no covers or superseded runs) | collector 4,268.71 / 705.74 / 20,210,589,568,747 B (= 4,264.81 + 3.89; 705.12 + 0.60) | yes |
| 4,711 / 740 CPU-h over every run | totals `all_runs` 4,711.11 / 740.44; 378,293 runs = 28 + 377,775 + 233 + 257 | yes |
| 232 residual, 1 final, 233 capped | `residual-pass-manifest.jsonl` 232 rows; `leaf:SOLVER_TIMEOUT` 233 | yes (n1 wording) |
| 598 native + 3 = 601; 607 (604 native); 604 (601 native) | release and capstone READMEs: "601 (3 standard + 598 native), 607 (3 + 604), 604 (3 + 601)" | yes |
| 891 imported modules, not a cold rebuild | release README: "all 891 imported object hashes matched"; "not a cold rebuild" | yes |
| H3: 408 parts (24 + 384), 411 printed | H3 integration README: "24 pair ... 384 triple ... (411 total)" | yes |
| H5: 40 parts + cover checks | H5 terminal review: 40 native search + 18 graph-cover (61 printed) | yes (n4) |
| $h=9$: 18 certificates | `Erdos85OrderFortyNineNineHighContradiction.lean` imports 18 `…Rep…Certificate` modules | yes |
| 43 classes = 15 counting + 28 structural | `sevenHighT0EmptyCube_counting_or_structural` (19 + 15 + 7 + 2) | yes |
| 17,633 vars, 720,825 clauses; hashes `fd601b82…`, `4d47ffdd…` | H7 README §1, §10 | yes |
| about \$215 of cloud compute | no linked receipt; campaign README has estimates only | **untraced (m3)** |

## Critical flags

None.

Hard scope rules re-checked:
- A-REG is a hypothesis with a stated rival.
- "First drop" stays epistemic ("To our knowledge ... at this level of evidence").
- cake_lpr is outside Lean in every mention.
- The `native_decide` dependence is disclosed with counts.
- Nothing is claimed about Erdős 85.
- R-AUD: 0 governance and 0 private-locator hits in the paper text.
- R-LINK: all 64 link targets exist at the pinned commit `1d0772cd825`, which is on `origin/erdos85/release-assembly-20261011`.

The BRIEF's "never call Result A a theorem" is discussed above as M3.

## Dimension summary

| # | Dimension | Weight | v9 | v10 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 |
| 2 | Evidence sufficiency | 6 | 4 | 5 |
| 3 | Clarity of contribution | 5 | 5 | 5 |
| 4 | Related-work positioning | 5 | 4 | 4 |
| 5 | Reproducibility | 5 | 4 | 3 |
| 6 | Figure & table quality | 4 | 4 | 4 |
| 7 | Prose & structural quality | 4 | 4 | 3 |
| 8 | Citation hygiene | 5 | 5 | 5 |
| 9 | Rhetorical economy | 4 | 4 | 3 |
| | **Total** | **44** | **39** | **37** |

- **Up.** D2 rose: H3 and H5 moved from reviewed arguments to Lean, and H7 ($t=0$) from a reviewed ledger to a complete, receipt-backed certificate campaign.
- **Down.**
  - D5 fell because the headline is now a Lean theorem that cannot be compiled from the published snapshot (M1).
  - D7 fell for the changelog voice ("now", "no longer needed").
  - D9 fell for the 11th page, which comes mostly from one dense paragraph of run logistics.
- **Net.** The evidence is stronger than v9; the presentation of the update is not yet as tight. Full justifications are in `scoring.md`.

## Top fixes (advisory; `advance: true`)

1. **M1 — state, or remove, the unpublished build inputs of the capstone.**
   - The 13 H7 $t\ge1$ certificate modules `include_str` absolute paths on a private volume, and `Erdos85OrderFortyNineCapstoneH3` imports them, so the stated theorem cannot be rebuilt from the repository.
   - Add this to the post-table "complete list" [L232] and to "What is not claimed" [L87].
   - Better: publish the 13 files and repoint `include_str` before tagging.
2. **M3 — BRIEF vs. abstract.** Either the operator adds an R-V10 BRIEF amendment (new `claim`; the hard rule becomes "never an unconditional Lean theorem"), or Abstract [L66] reads: "Lean derives the upper side from two explicit unsatisfiability hypotheses, $h_{\mathrm{H1}}$ and $h_{\mathrm{H7}}$, which the external checks support but which are not admitted into Lean."
3. **M2 — the linked strata receipt.** At the pinned commit, `STRATA_AND_SMALL_ORDERS_20260928.md` still describes H5 as a reviewed cover and the H7 capstone as uninstantiated. Banner it as superseded, or drop it from §8 [L277].
4. Then the minors in one pass:
   - "four strata" (m1);
   - "at depth 3" (m2);
   - delete or source the \$215 (m3);
   - "by emitters" (m4);
   - version-history voice (m7);
   - move the pass/cap narrative to the README (m8).

## Evidence drift

`anvil.lib.evidence_drift` reports NO-SNAPSHOT: v10 was a direct edit and recorded no `evidence_snapshot`. That is treated as clean, so there is no automated note. By hand: `refs/` gained seven files on 2026-10-11, and they support v10. `BRIEF.md` was not amended, and its `claim` and hard rule now lag the paper (M3). Advisory only; this changes no score and no gate.
