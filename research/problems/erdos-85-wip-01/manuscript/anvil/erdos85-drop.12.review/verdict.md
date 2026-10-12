# Verdict — erdos85-drop.12

**Total: 41 / 44** (prior iteration `erdos85-drop.11.review/`: 40 / 44)

**Decision: `advance: true`.** The total clears the 35-point threshold and no critical flag is set. The pending-marker gate passed (0 markers), so the rubric gate gives `ready: true`. The version-dir `_progress.json` still lists a fresh author audit of the final combined version as an outstanding process dependency. Major M1 should be fixed before that audit and before the tag.

v12 is iteration 12 of `max_iterations: 8`, a direct-edit pass beyond the cap. It reports three things: publication of the 13 packed H7 certificate files (Requester Pays, with a fetch script and SHA256 manifest), an accepted cold rebuild of the 893-module closure (attempt 2; attempt 1's failure is retained), and a second rebuild from a checkout without the files, which fetched them with the script and produced byte-identical objects. It also applies the v11 review fixes. All claims were checked against the pin `fa2b41268df024128ed4738b3bb500637cf1ec12`. No Lean was compiled for this review.

## Resolution of the v11 findings

| v11 finding | Status in v12 | Evidence |
|---|---|---|
| Release precondition: the capstone could not be rebuilt from public inputs | **Resolved** | 13 files published with fetch script and manifest (L87, L280). Attempt-2 `ACCEPTED.md`: 893/893, audit PASS, 601/607/604. Third-party-path `ACCEPTED.md`: byte-identical `.olean` objects for all 893 modules. |
| m1: H7 not positioned against the hexagon precedent | Resolved | "For H7, Lean verifies the soundness of the symmetry-breaking extension and the composition of cover and leaf UNSAT hypotheses." (§3 [L153]) |
| m2: publication filed under "fully independent audit" | Resolved | L232 separates "The formal gaps" from "Reproducibility is a separate issue". |
| m3: Table 2 column category | Mostly resolved | "nothing; not standard-axiom-only; replayed in the cold rebuild". The replay notes remain in the "Open in Lean" column (m3). |
| m4: H7 paragraph density / length | Paragraph resolved; length worse | Cap and timeout narrative removed. Main text is now about 12 pp (references start on p. 13) (m7). |
| n1 to n5 | Resolved | "is superseded"; "\$225 … (controller estimates; …)"; "previously known"; the ceiling clause is gone from the H7 README at the pin; "40 search parts and 18 cover and cardinality checks". |
| BRIEF advisory (stale `claim`) | Resolved | The frontmatter `claim` and the 2026-10-11 evidence update match the paper. |

## Overclaiming sweep (new edits)

The new rebuild and publication sentences were read for overclaiming. The rebuild is presented as reproducibility, not as a change of formal status: "That rebuild still lists the `native_decide` axioms, as any rebuild would" (L232), and Table 2 keeps "the two hypotheses" as the open item for the upper side. The paper's "starting from a checkout without the certificate files and obtaining them with the published download script" matches the third-party `ACCEPTED.md`. The paper does not call it a third-party rebuild, and the bucket-owner-credentials limitation is disclosed (L280). "Byte-identical compiled objects for all 893 modules and the same axiom lists" matches `reproducibility-vs-attempt2.json` as summarized in `ACCEPTED.md`. **No overclaim was introduced.**

## Critical flags

None. Hard scope rules re-checked:
- **Result A is never called a theorem.** The upper side is "derived in Lean … from exactly two hypotheses" ($h_{\mathrm{H1}}$, $h_{\mathrm{H7}}$ with $t=0$), checked externally by cake_lpr. Every "Lean theorem" near Result A is a negation.
- **`native_decide` is disclosed** with counts (598 in the abstract, 601/607/604 in §2.2 and Table 2).
- **cake_lpr is outside Lean** in every mention.
- **Nothing is claimed about Erdős Problem 85** ("Nothing is claimed about Erdős Problem 85 itself").
- **A-REG is not asserted** ("$\AREG$ is not asserted"; it is a hypothesis with a stated rival).
- **R-AUD:** 0 governance and 0 private-locator sentences in the paper.
- **R-LINK:** 70/70 distinct targets exist at the pin. The printed commit is wrong (M1), but the links themselves resolve.

## Major findings

- **M1 — §8 [L272]: the stated snapshot commit is wrong.** The text says the linked material is in the repository "at commit `92ff6248033c`". Every link goes to `fa2b41268df`. At `92ff6248033c` the three rebuild records the paper cites do not exist: both `ACCEPTED.md` files and `FAILURE.md`. Fix: print the `\repobase` commit (or the final tag), preferably derived from the same macro.

## Dimension summary

| # | Dimension | Weight | v11 | v12 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 6 | 6 |
| 2 | Evidence sufficiency | 6 | 5 | 6 |
| 3 | Clarity of contribution | 5 | 5 | 5 |
| 4 | Related-work positioning | 5 | 4 | 5 |
| 5 | Reproducibility | 5 | 4 | 4 |
| 6 | Figure & table quality | 4 | 4 | 4 |
| 7 | Prose & structural quality | 4 | 4 | 3 |
| 8 | Citation hygiene | 5 | 5 | 5 |
| 9 | Rhetorical economy | 4 | 3 | 3 |
| | **Total** | **44** | **40** | **41** |

## Remaining fixes (advisory; `advance: true`)

1. **M1:** replace `92ff6248033c` at L272 with the pin or tag that `\repobase` uses.
2. **m1:** repin to a release-assembly commit that contains the corrected fetch-script credential comment (the pinned copy says "any AWS credentials work"). Ideally, test the fetch from a non-owner AWS account.
3. **m2:** add a superseded banner to `FAILURE.md`, whose last line says "The manuscript must not claim a completed cold project rebuild". Trim the budget and authorization clauses from the linked cold-build README.
4. **m4:** finish the open independent re-audit of the rebuild bundle, or say in §2.2 that the rebuild audit is automated and an independent re-audit is pending.
5. **m5 / m6:** fix the four space-less link labels ("campaigntotals", "censusreceipts", "bankreceipts", "cold-buildrecipe"), and name the September 2026 cold axiom audit at L93 and L236.
6. **m3 / m7 / nits:** move the replay notes out of the "Open in Lean" column; tighten §2.2 if a page matters; update `\date`; run one more LaTeX pass to clear the final-pass "Rerun" warning.

## Evidence drift

`anvil.lib.evidence_drift` reports NO-SNAPSHOT (v12 is a direct edit) and treats that as clean, so there is no automated note.
