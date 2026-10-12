# Verdict — erdos85-drop.13

**Total: 43 / 44.** The prior iteration, `erdos85-drop.12.review/`, scored 41 / 44, and `erdos85-drop.12.audit/` returned BLOCK on C1.

**Decision: `advance: true`.** The total clears the 35-point threshold, no critical flag is set, and there are no major findings. The pending-marker gate passed with 0 markers, so `ready: true`. This review clears the review side only. The v12 audit's BLOCK (C1) applies to v12, and C1 is fixed in v13, but AUDITED needs a fresh paper-audit of v13. The version-dir `_progress.json` lists that audit as outstanding.

v13 is iteration 13 of `max_iterations: 8`, a direct edit made beyond the cap. It changes 14 source lines, repins every link to `2029149d7e42b74036ff0e1e82af6d33c2e32748`, and introduces a single `\repocommit` macro that drives both the links and the printed commit. All claims were checked at that pin. No Lean was compiled for this review.

## Resolution of the v12 findings

Every row of the v13 changelog table was checked against the pin:

| v12 finding | Status | Evidence |
|---|---|---|
| Audit C1 / review M1: wrong snapshot commit | **Resolved** | The printed commit is `\repocommitshort` (PDF: "2029149d7e42"). The 70/70 PDF URIs use the full hash and resolve. The three rebuild records exist at the pin, which is on `origin`. |
| Audit M1 / review m4: independent re-audit open | **Resolved** | `ACCEPTED.md` at the pin records the Codex re-audit as PASS, confirmed in the squad `review_requests` row 2749. L113 now says "repeated independently by a second AI author". |
| Review m1: fetch-script comment | **Resolved** | The pinned comment says credentials were "tested so far only with credentials of the bucket owner's account". |
| Review m2: records hygiene | **Mostly resolved** | The banner, path and account-number fixes landed. Residue: the README still has "separate spending authorization" and "10-hour budget", `FAILURE.md` still has a local path, and `ACCEPTED.md` cites "squad review #2749" (minor m2). |
| Review m3: Table 2 column | **Resolved** | L225, L228. |
| Review m5: run-together labels | **Resolved** | Single-token labels. |
| Review m6: ambiguous cold builds | **Resolved** | "September 2026 cold axiom audit" at L95 and L238. |
| Audit minors ("second" rebuild; "not published") | **Resolved** | L113, L282. |
| Nits (date, rerun warning) | **Resolved** | 12 October 2026. No rerun warning in the log. |
| Review m7: length | **Declared not addressed** | Minor m1. |

## Critical flags

None. Hard scope rules re-checked:
- **Result A is never called an unconditional Lean theorem** ("Result A is not an unconditional theorem of Lean"). Lean derives the upper side from exactly the two hypotheses, $h_{\mathrm{H1}}$ and $h_{\mathrm{H7}}$ with $t=0$, which cake_lpr checked outside Lean. The 598 `native_decide` axioms and the emitter gap are disclosed.
- **Nothing is claimed about Erdős Problem 85** ("Nothing is claimed about Erdős Problem 85 itself").
- **A-REG is not asserted**: Theorem B is an implication, and A-REG has a stated rival.
- **R-AUD**: the paper has 0 governance and 0 private-locator sentences. **R-LINK**: 70/70 targets exist at the pin.

## Major findings

None.

## Dimension summary

| # | Dimension | Weight | v12 | v13 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 6 | 6 |
| 2 | Evidence sufficiency | 6 | 6 | 6 |
| 3 | Clarity of contribution | 5 | 5 | 5 |
| 4 | Related-work positioning | 5 | 5 | 5 |
| 5 | Reproducibility | 5 | 4 | 5 |
| 6 | Figure & table quality | 4 | 4 | 4 |
| 7 | Prose & structural quality | 4 | 3 | 4 |
| 8 | Citation hygiene | 5 | 5 | 5 |
| 9 | Rhetorical economy | 4 | 3 | 3 |
| | **Total** | **44** | **41** | **43** |

## Remaining fixes (advisory)

1. **m1 (D9):** main text is about 12 pp against ~10. Collapsing the three §2.2 rebuild sentences into one is the cheapest cut.
2. **m2 (records, outside the paper):** trim "separate spending authorization" and "approximate 10-hour budget" from the linked README, the local archive path from `FAILURE.md`, and "squad review #2749" from `ACCEPTED.md` before the tag.
3. **Nits:** use one name for the September audit in Table 2; refresh the BRIEF evidence-update paragraph.
4. **Process:** run a fresh `paper-audit` on v13 to reach AUDITED. At publication, cut the release tag at `2029149d7e42`. That commit is on `origin/erdos85/release-assembly-20261011`, not on the paper branch, so the tag must point at the assembly commit. A fetch from a separate AWS account remains untested; this is disclosed and does not block.
