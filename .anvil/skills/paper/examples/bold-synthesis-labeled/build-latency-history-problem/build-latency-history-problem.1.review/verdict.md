# Verdict — build-latency-history-problem.1 (paper-review)

**Reviewer scope**: the /44 `anvil-pub-v2` rubric over `main.tex`. The parallel
`paper-audit` owns per-`\cite{}` claim support and numeric cross-checking; not
duplicated here.

## Decision

**ADVANCE.** Total **43/44** (≥ 35 advance threshold). Critical flags: **none**.

`advance: true` — total is above threshold and there are zero unresolved
critical flags. The paper stakes a claim substantially larger than its
sibling fixture (`../../../underclaiming-buried-lede/`) on identical
evidence, and takes **no** overclaiming deduction for doing so, because it
labels which components are inherited, which are demonstrated, which are
derived, and which are conjecture.

## Ambition-versus-inflation check

Per `rubric.md` §"Ambition is not novelty inflation", the reviewer separated
the *size* of the claim from its *labelling*:

| Question | Result |
|---|---|
| Is a synthesis / framing / research-program claim staked? | **Yes** — in the title, the abstract's first sentence, and §1's opening. |
| Are inherited ingredients labelled as inherited? | **Yes** — §1's *Synthesis* item and §2 both name co-change mining and speculative warming as mature and not the authors'. |
| Is any conjecture presented as a result? | **No** — the test-selection extension is labelled *Conjecture*, given a falsifiable form, and repeated as conjecture in §5. |
| Is novelty asserted without a specific search? | **No** — the four related-work clusters each name the closest work and what is taken from it. |
| Deduction taken for ambition alone? | **No.** |

The bold claim is scored on its labelling, not on its size. Had the same
sentence appeared without the evidentiary split — or had the conjecture been
written in the present indicative — the ordinary dim 3 / dim 9 scoring and
the critical-flag path would have caught it; neither fired here.

## Underclaiming / buried-lede check

Not raised. The cold-reader pass over the abstract and introduction alone:

| Cold-reader question | Result |
|---|---|
| Central idea extractable from abstract + introduction alone? | **Yes** — "history is a scheduling input". |
| Extractable idea matches the brief's strongest honest claim? | **Yes** — it is the brief's §"Strongest claim" sentence, near-verbatim. |
| Claim stated before the qualification apparatus? | **Yes** — the limits arrive in §5, after the claim and its evidence. |
| Could the title describe fifty adjacent papers with noun substitutions? | **No.** |

## Critical flags

None.

- **Citation error**: not raised. Every `\cite{}` resolves to a complete entry.
- **Missing experiment for a claim**: not raised. The one claim without an
  experiment is labelled a conjecture and carries the experiment that would
  test it.
- **Numerical inconsistency**: not raised. Abstract, §1, Table 1, Table 2, and
  §4.3 agree (8.3 / 71.4; 0.87 against 0.71; 9.1 / 7.4 / 22.4; 31.1; 5.8).
- **Close prior work ignored**: not raised.

## Dimension summary

| # | Dimension | Weight | Score |
|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 6 |
| 2 | Evidence sufficiency | 6 | 6 |
| 3 | Clarity of contribution | 5 | 5 |
| 4 | Related-work positioning | 5 | 5 |
| 5 | Reproducibility | 5 | 5 |
| 6 | Figure & table quality | 4 | 3 |
| 7 | Prose & structural quality | 4 | 4 |
| 8 | Citation hygiene | 5 | 5 |
| 9 | Rhetorical economy | 4 | 4 |
| | **Total** | **44** | **43** |

## Top revision priorities

None blocking. One optional improvement carried in `comments.md`: Table 2's
caption should state what the ablation shows, not only where its numbers come
from (dim 6, the pair's shared deduction).

## What's working — do NOT weaken if a further revise occurs

- The labelled contribution list. Deleting the labels to "tighten" §1 would
  convert a properly-scoped bold claim into an unlabelled one and cost dim 3.
- The falsifiable form of the conjecture, including the named null result that
  would confine the claim to cache warming.
- §2's refusal to collapse the paper to its least-novel ingredient while still
  saying plainly that the ingredient is inherited.
