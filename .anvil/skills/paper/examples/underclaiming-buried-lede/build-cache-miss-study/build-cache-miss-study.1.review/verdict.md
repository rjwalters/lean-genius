# Verdict — build-cache-miss-study.1 (paper-review)

**Reviewer scope**: the /44 `anvil-pub-v2` rubric over `main.tex`. The parallel
`paper-audit` owns per-`\cite{}` claim support and numeric cross-checking; not
duplicated here.

## Decision

**REVISE.** Total **33/44** (< 35 advance threshold). Critical flags: **none**.

`advance: false` on the score alone. This is the case the rubric's dim 3 / dim 9
symmetry (issue #1046/#1047) exists to catch: a paper with no defect a
program-committee member could point to, and no reason for that member to
remember it. Rigor (6/6), evidence sufficiency (6/6), reproducibility (5/5),
and citation hygiene (5/5) are all at full weight — every one of the 22 points
those four dimensions carry. The paper still fails, on the four dimensions
that ask what it is *for*.

## Underclaiming / buried-lede finding

**Severity: `blocker`** (`comments.md` §"Underclaiming / buried-lede"). The
cold-reader check in `commands/paper-review.md` step 5 was run against the
abstract and introduction alone:

| Cold-reader question | Result |
|---|---|
| Central idea extractable from abstract + introduction alone? | **No** — a reader extracts a measurement and a prototype. |
| Extractable idea matches the brief's strongest honest claim? | **No** — the brief's §"Strongest claim" names history-as-a-scheduling-signal; the paper's extractable idea is a miss-distribution statistic. |
| Claim stated before the qualification apparatus? | **No** — two paragraphs of scope-limiting precede the contribution list. |
| Could the title describe fifty adjacent papers with noun substitutions? | **Yes** — "An Empirical Characterization of X in Y". |

The finding is `blocker` rather than `major` because the buried idea is the
paper's entire reason for existing: the brief describes a research program
about where history belongs in a build system, and the draft reads as a
narrow implementation note about one cache. This is a **finding, not a
critical flag** — nothing here would make a sophisticated reader stop taking
the paper seriously, which is precisely why the old rubric let it through.

## Critical flags

None.

- **Citation error**: not raised. Every `\cite{}` resolves to a complete entry.
- **Missing experiment for a claim**: not raised. The paper claims less than
  its evidence supports, which is the opposite defect and is not a flag.
- **Numerical inconsistency**: not raised. Text, Table 1, and Table 2 agree
  (pooled 8.3 / 71.4; ablation 9.1 / 7.4 / 22.4 matching §4.3).
- **Close prior work ignored**: not raised. All four clusters are engaged.

## Dimension summary

| # | Dimension | Weight | Score |
|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 6 |
| 2 | Evidence sufficiency | 6 | 6 |
| 3 | Clarity of contribution | 5 | 1 |
| 4 | Related-work positioning | 5 | 3 |
| 5 | Reproducibility | 5 | 5 |
| 6 | Figure & table quality | 4 | 3 |
| 7 | Prose & structural quality | 4 | 3 |
| 8 | Citation hygiene | 5 | 5 |
| 9 | Rhetorical economy | 4 | 1 |
| | **Total** | **44** | **33** |

## Top 3 revision priorities

1. **Re-title and re-abstract around the strongest claim.** The brief's
   §"Strongest claim" states it in one sentence; put that sentence first, and
   demote the 8.3 / 71.4 measurement and the 22.4 deployment number to the
   evidence position they actually occupy.
2. **Label the contribution list by evidentiary status.** Demonstrated,
   derived, synthesis, conjecture. The Discussion's disowned framing paragraph
   is a conjecture worth stating in falsifiable form, not worth deleting.
3. **Re-position related work at synthesis scope.** Keep the honest "the
   predictor is inherited" statement; add the claim the section currently
   omits — that reading history *online, in the scheduler* is what the paper
   is arguing for, and that no cited cluster does it.

## What's working — do NOT weaken in revision

- The attribution definition and its sensitivity re-run (§3.1, §5).
- The ablation and its non-redundancy reading (§4.2, §4.3) — this is the
  evidence for the buried claim and needs no strengthening, only promotion.
- The threats-to-validity paragraph. Revising toward a bolder framing must not
  cost the paper any of this; the target is a *labeled* bold claim, not hype.
