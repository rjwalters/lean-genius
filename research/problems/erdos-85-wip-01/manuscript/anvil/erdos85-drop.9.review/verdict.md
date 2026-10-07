# Verdict — erdos85-drop.9

**Total: 39 / 44** (prior iteration `erdos85-drop.8.review/`: 39 / 44, scored before the H3 error was known)

**Decision: `advance: true`.** The total clears the 35-point threshold and no critical flag is set. The pending-marker gate passed (0 markers), so `ready: true`. This is iteration 9 of `max_iterations: 8`, an operator-override pass (`metadata.operator_override: true`). It is the last authorized pass, so the fixes below go to the operator (or to `paper-audit`) as small direct edits, not another lifecycle iteration.

**Mid-review title change.** During this review the operator retitled the paper to "A Drop at Forty-Nine in Erdős Problem 85" (BRIEF amendment R-TITLE). That edit is in `erdos85-drop.9/main.tex` L56, and the `git diff` shows it is the only change to `main.tex`. This review scores the updated source. `main.pdf` (10:02) predates the edit (10:08), so it still shows the old title. `_gate.json` was computed on that PDF. A one-line title change cannot add overfull boxes in the body, but the PDF must be rebuilt (the operator will do this) before it is the manuscript of record.

## Re-evaluation of the five `erdos85-drop.8.operator` flags

1. **H3 evidence misstated: resolved.** §2.3 now says "no SAT verdict or LRAT proof exists for either cell formula, and in Lean the two exclusions are undischarged hypotheses". H3 is described as a reviewed graph-to-core argument with exhaustive Python enumerations. The counts (3,337 for $t=1$; 972 for $b=0$; 3,600 for $b=1$) match `Q7_H3_PROFILE_EXCLUSION_20260910.md`. The claim that "the two $t=0$ searches were replayed from unchanged source with no time limit" matches that note's full-completion reviews 1679/1681. Both Lean names exist and have the stated shapes: `threeHighCanonicalGraphCover_all` L530 and `orderFortyNineStratumExcluded_three_of_representativeExclusions` L537 of `Erdos85OrderFortyNineThreeHighOneFiber.lean`. The Q7 note is linked, and its public copy on `origin/erdos85/integration` is byte-identical to the ref. The formula-size and LRAT pointers are gone. Table 2's H3 row and the "What is not claimed" paragraph agree with `H3_EVIDENCE_AUDIT_20261007.md`. A sweep of every H3 mention (abstract, Result A, §1, §2.3, Table 2, post-table, §8) found no remaining sentence that implies H3 has a certificate or an unnamed checker.
2. **Scope of "certificate-checked": resolved, with one wording defect (M1).** The term now appears only for H1 (abstract, §1 "What is new", Table 1) and for H7 $t\ge1$ (Result A, "checked inside Lean", with the `Lean.ofReduceBool` dependence stated). With the new title, it no longer appears in the title at all. The abstract carries the strata tags and says the upper bound "also depends" on the reviewed arguments. The defect: the abstract and Result A call the H5 and H7 ($t=0$) computation "independently replayed". The receipts, the H3 evidence audit, the BRIEF claim and the paper's own §2.3 and Table 2 all say "independently checked", and §2.3 says one H7 $t=0$ source enumeration "rests on an audit of the enumerator code rather than an independent replay".
3. **Hexagon comparison on one axis: resolved,** apart from an antecedent slip (m1): "Both works" grammatically refers to the two hexagon papers.
4. **`LRAT.check` clause / §8 wording / 24-hour cap: resolved.** The §8 checker text matches `CHECKING.md`.
5. **refs.bib: resolved.** Capitals are protected, `heule2024hexagon` has pages 61--80 and no volume, and the build was at its fixpoint before the title edit.

## Title check (R-TITLE, resolved by the operator)

"A Drop at Forty-Nine in Erdős Problem 85" does not overclaim:
- It asserts only that a drop occurs at order 49, which is the content of Result A.
- It drops "certificate-checked", which no longer described the whole drop once H3 was corrected.
- It uses no "theorem", "proof" or "decided".
- It says nothing about the answer to the problem.

The abstract qualifies the drop in its first paragraph ("as a computational result"; "The result is not a Lean theorem"; "one drop is compatible with either answer to the problem"). A computational paper stating its result in the title is ordinary practice. It does not underclaim either: Theorem B is the abstract's second paragraph and §1's second display. Optional nit n5: the section heading "The drop at 48 to 49" could match the title's wording.

## Critical flags

None.

Hard scope rules re-checked:
- Result A is never called a theorem, proof or "decided".
- cake_lpr is stated to be outside Lean.
- Both H1 open items appear in the abstract, §1, §3.4 and Table 2.
- The `native_decide` dependence of the witnesses, the H1 cover and the H7 modules is disclosed.
- Nothing is claimed about Erdős 85 itself.
- A-REG is a hypothesis with a stated rival.
- "First drop" is epistemic ("To our knowledge ... at this level of evidence").
- R-AUD: 0 governance and 0 private-locator hits.
- R-LINK: the six unlinked-path hits are `\repofile` false positives.

## Dimension summary

| # | Dimension | Weight | v8 | v9 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 |
| 2 | Evidence sufficiency | 6 | 5 | 4 |
| 3 | Clarity of contribution | 5 | 5 | 5 |
| 4 | Related-work positioning | 5 | 4 | 4 |
| 5 | Reproducibility | 5 | 4 | 4 |
| 6 | Figure & table quality | 4 | 4 | 4 |
| 7 | Prose & structural quality | 4 | 4 | 4 |
| 8 | Citation hygiene | 5 | 4 | 5 |
| 9 | Rhetorical economy | 4 | 4 | 4 |
| | **Total** | **44** | **39** | **39** |

The totals match, but the scores mean different things. v8's D2 credited an H3 certificate that did not exist. v9's D2 is lower because the drop now honestly rests on three reviewed arguments and the abstract describes them one notch too strongly (M1). D8 rose because the uncited `LRAT.check` clause is gone. Full justifications are in `scoring.md`.

## Top fixes (advisory; `advance: true`)

1. **M1: one word, two places.** Abstract [L66]: "reviewed arguments with independently replayed computation (H3, H5; H7, $t=0$)" → "independently checked computation". Result A [L78]: the same change. Keep "replayed" in Table 2's H3 row and in §2.3, where the H3 ref supports it.
2. **M2: the linked receipt `STRATA_AND_SMALL_ORDERS_20260928.md` contradicts the paper.** This is outside `main.tex`.
   - The copy on `origin/erdos85/integration`, which `\repobase` points to, still says H3 has "checked LRAT proofs for both cells". The correction exists only on `origin/erdos85/paper-v6` (`13400a4c890`).
   - In both copies, the H1 row still says "1,257 rows ... the row-to-stratum assembly is an open formal obligation", which contradicts §2.4 and Table 2 (R-BRIDGE).
   - Fix the H1 row (or add a "superseded" banner) and merge paper-v6 into integration before the tag or Zenodo step.
3. **m1:** §3 [L137] "Both works reduce ..." → "The hexagon verification and ours both reduce ...". After that, rebuild the PDF with the new title, as already planned.

## Evidence drift (advisory only)

`anvil.lib.evidence_drift` reports **EVIDENCE-DRIFT** on `BRIEF.md` only; `refs/**` is unchanged since v9's snapshot. The changes are the R-H3 amendment with the corrected frontmatter `claim`, and the mid-review R-TITLE amendment with the new frontmatter `title`, all dated 2026-10-07. I re-read them against v9. The paper agrees with R-H3 in substance, the withdrawn "name the H3 checker" request is no longer applied, and the title matches R-TITLE. The new claim's wording, "reviewed arguments with independently checked computation (H3, H5, H7 t = 0)", is the basis for M1. This note does not change `advance`, any score, or the terminal gate.
