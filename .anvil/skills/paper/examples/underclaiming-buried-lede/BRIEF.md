---
project: underclaiming-buried-lede
audience:
  - Systems / software-engineering program committee members reading a build-infrastructure submission
max_iterations: 4
documents:
  - slug: build-cache-miss-study
    artifact_type: paper
---

# Fixture A — the rigorous paper that buries its own contribution

This project is **Fixture A** of the underclaiming / buried-lede regression
pair shipped with `anvil:paper` (issues #1046 → #1047 → #1048). It exists to
prove that the rubric criteria shipped in #1047 actually catch the failure
mode #1046 describes: *a safe, polished, fully-sourced, technically
unobjectionable paper that never states its reason for existing.*

The paper is deliberately good at everything the rubric already rewarded
before #1047 — the method is sound, the ablation isolates the contributing
signals, the seeds and hyperparameters are recorded, every non-trivial claim
carries a citation, and the bibliography entries are complete. It is
deliberately bad at exactly one thing: the organizing idea named in
`build-cache-miss-study/BRIEF.md` §"Strongest claim" never reaches the title,
the abstract, or the contribution list. It surfaces once, hedged, in the last
paragraph of the Discussion.

Its sibling, `../bold-synthesis-labeled/`, reports the **same measurements
from the same trace with the same bibliography** — the Method-through-Experiments
span of the two bodies is byte-identical — and states the organizing idea
first, labeling which ingredients are inherited. The recorded reviews score
the two 33/44 and 43/44.

## Everything here is synthetic

The organization, the three repositories, the 2.1M-invocation trace, every
measurement, and every bibliography entry are **invented for the fixture**.
Nothing in this project reports a real system or a real result, and the
bibliography must not be cited. The numbers exist so the fixture can be
internally consistent (text against tables, ablation against the deployment
claim) the way a real paper under audit must be.

## What the recorded review shows

`build-cache-miss-study/build-cache-miss-study.1.review/` is a recorded
`paper-review` pass under the post-#1047 criteria. Its verdict:

- **33/44, `advance: false`** (threshold ≥35), with **zero critical flags**.
- Full weight on dim 1 *Rigor* (6/6), dim 2 *Evidence sufficiency* (6/6),
  dim 5 *Reproducibility* (5/5), and dim 8 *Citation hygiene* (5/5).
- A named **`underclaiming_buried_lede`** finding at `blocker` severity, from
  the cold-reader check in `commands/paper-review.md` §"Underclaiming /
  buried-lede finding".
- The deductions land only where #1047 says they should: dim 3 *Clarity of
  contribution* (1/5), dim 4 *Related-work positioning* (3/5), dim 7 *Prose &
  structural quality* (3/4), and dim 9 *Rhetorical economy* (1/4).

That combination — high rigor, high citation hygiene, sub-threshold total — is
the whole point: before #1047 this paper scored like a solid submission,
because nothing in the rubric asked whether it had a reason to exist.

See `../README.md` for the pair's regression contract and
`../../tests/test_paper_underclaiming_fixtures.py` for the assertions.
