# Verdict — erdos85-drop.8

**Total: 39 / 44** (prior iteration `erdos85-drop.7.review/`: 35 / 44)

**Decision: `advance: true`.** The total clears the 35-point threshold and no critical flag is set. The pending-marker gate passed (0 markers), so `ready: true`. The thread may proceed to `paper-audit`. This is iteration 8 of `max_iterations: 8`. The remaining items in `comments.md` (1 major, 5 minor, 6 nit) are inputs to the audit or to an operator-directed polish pass. None blocks.

## Re-evaluation of the v7 critical flag

**`close_prior_work_ignored`: resolved.** §3 now cites both `heule2024hexagon` (Heule and Scheucher, TACAS 2024) and `subercaseaux2024hexagonlean` (Subercaseaux et al., ITP 2024) through `\citet`. Both entries resolve in `refs.bib` with DOIs, and §1 "What is new" (2) points to the positioning. The paragraph does what R-V8 §2 asks:

- It names the precedent as the closest one.
- It says theirs is stronger on encoding faithfulness: "On encoding faithfulness their result is stronger than ours" [L138].
- It claims only specific, checkable differences: a whole-stratum Lean reduction to 13,351 formulas, about 28 TB checked by cake_lpr, hash-only check-then-discard with byte-identical regeneration, re-validation of the 22.55 TB bank, and a public checker.

The v7 sentence that read as if the Lean-formula plus verified-checker pairing were new ("Our contribution is to run this discipline …") is gone. Novelty is not overclaimed.

One residual imprecision remains, recorded as major M1 rather than a flag. The contrast sets their encoding proof against our file-to-formula link, although the paper's own H1 encoding is also Lean-verified (with `native_decide`). It undersells this paper more than it overstates it.

## Critical flags

None.

Checked against the hard scope rules (all held; detail in `findings.md` §2):

- **Result A.** It is never called a theorem, proof or "decided". The text says "Result A is not a theorem of Lean" (§1), and the abstract says "The result is not a Lean theorem".
- **"Formally verified checker".** The phrase is used only for H1, plus once for the cited precedent. H3 is "checked LRAT proofs", with the checker stated as not recorded. H7 $t\ge1$ is "certificates checked inside Lean". H5 and H7 $t=0$ are "reviewed arguments".
- **cake_lpr outside Lean.** The paper says "a HOL4 theorem about its compiled binary, not a Lean kernel check" (§3.4), and the Table 1 caption says "All checks ran outside the Lean kernel".
- **Both H1 open items.** (i) "external checks not admitted into Lean" and (ii) "file = formula via the compiled emitter" are named in the abstract, §1 "What is not claimed", §3.4, Table 2 (numbered (i)/(ii), naming `v2cnf`) and the post-table paragraph.
- **H1 cover theorem axioms.** The paper says "the three standard ones and 23 `native_decide` axioms, no `sorryAx`", which matches the receipt (I counted 23). The receipt is linked. The H1-reduction row reads "Open: nothing; not standard-axiom-only", as R-BRIDGE requires.
- **Erdős 85.** Nothing is claimed about the problem itself: "one drop is compatible with either answer".
- **A-REG.** It is "a hypothesis with a stated rival", and the plane-order rival is stated in §5. Its $q=4$ analogue is now refuted through the explicit `sixteenRegular` witness, which I checked in `Erdos85Problem.lean`.
- **R-AUD.** The audience pre-flight found 0 governance and 0 private-locator hits. The six unlinked-path hits are `\repofile` false positives. "$225" is a reader-facing cost fact. The Walters credit is neutral, per the Authorship amendment.
- **R-LINK.** There are 49 distinct `\repofile` targets, all present. 40 are on `origin/erdos85/integration`. 9 are on `origin/erdos85/paper-v6`: `CHECKING.md`, `h1_checker_kit/`, the bank-check dir and its 3 receipts, `historical96_cake_lpr_receipts.jsonl`, `COMPOSITION_AXIOMS_…` and `H1_COVER_AXIOMS_…`. They land with the merge, which is not a defect. The bucket name is kept out of the paper.

## Numbers against receipts (recomputed)

- **H1 partition.** 12,094 (bank TSV, all VERIFIED, heap 8000 MB) + 1,160 (census TSV) + 96 (historical cake_lpr JSONL, all `CAKE_LPR_VERIFIED`, checker `d23c413b…`) + 1 (`81494a6ef36d3ec9`) = **13,351**. The sets are pairwise disjoint, and their union is exactly 13,351. **cake_lpr checked all of them**, the hardest via 36 leaves (all VERIFIED, 4 GB heap, 47.07 GB, largest 8.24 GB).
- **Historical.** 103,469,269,771 B ≈ **0.10 TB**, largest 2.49 GB. The 96 LRAT sha256 values are identical to the earlier pass.
- **Bank.** 22,554,276,624,018 B = **22.55 TB**; 6.29 TB gz; max 26.5 GB; 408.5 h; 21 CNF_MISMATCH ledgers.
- **Census.** 5.64 TB; 36.2 GB; 3,434.7 / 207.1 CPU-h (checking ≈ 6.0%); 1,075 rows at 4 GB and the maximum at 16 GB; 1,157 Graviton + 3 Mac; 1,163 + 30 + 3 = 1,196 ledgers.
- **Total.** 22.554 + 5.641 + 0.103 + 0.047 = **28.35 TB ≈ 28 TB**.
- **Cost.** $204 (census README) + $20.42 (bank summary) ≈ **$225**, scoped in the paper to "the census and the bank re-check".
- **Abstract.** **1,767 rendered characters** and 1,819 TeX-source characters, both ≤ 1,920 (v7: about 2,000).
- **Inventory.** 13,541 − 190 = 13,351. The H3 formula size (29,500 / 1,328,183) traces to `PHASE_B_H1_H3_INVENTORY`.

## Dimension summary

| # | Dimension | Weight | v7 | v8 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 |
| 2 | Evidence sufficiency | 6 | 5 | 5 |
| 3 | Clarity of contribution | 5 | 4 | 5 |
| 4 | Related-work positioning | 5 | 2 | 4 |
| 5 | Reproducibility | 5 | 4 | 4 |
| 6 | Figure & table quality | 4 | 3 | 4 |
| 7 | Prose & structural quality | 4 | 4 | 4 |
| 8 | Citation hygiene | 5 | 4 | 4 |
| 9 | Rhetorical economy | 4 | 4 | 4 |
| | **Total** | **44** | **35** | **39** |

Full justifications are in `scoring.md`.

## Highest-leverage remaining fixes (advisory; `advance: true`)

1. **M1: put the hexagon contrast on one axis.** State that H1's encoding is also Lean-verified (with 23 `native_decide` axioms), and locate the weaker link precisely: `native_decide` in the reduction, and file-to-formula through the compiled emitter. Confirm what the precedent does for its DIMACS file through `paper-litsearch` before claiming more.
2. **m1/m2: two small precision edits.** Drop or cite the single `LRAT.check` mention. Consider scoping "certificate-checked" in the title/abstract to H1, which needs an operator decision on the title.
3. **m4: §8 checker wording.** For historical orbits (and the 3 macOS census rows), a reader's re-solve is a fresh cake_lpr check, not a hash comparison with ours.

## Evidence drift (advisory only)

`anvil.lib.evidence_drift` reports **EVIDENCE-DRIFT** on `BRIEF.md` only; `refs/**` is unchanged since v8's snapshot. The change is the 2026-10-07 frontmatter `claim` update aligning the BRIEF with R-BRIDGE. I re-read the new claim against v8, and it is consistent: H1 is reduced in Lean to 13,351 formulas, all cake_lpr-checked; H3/H5/H7 are closed as stated; and the result is not a Lean theorem, for exactly the two H1 reasons plus the open H5 premises and H7 $t=0$ capstone. This note does not change `advance`, any score, or the terminal gate.
