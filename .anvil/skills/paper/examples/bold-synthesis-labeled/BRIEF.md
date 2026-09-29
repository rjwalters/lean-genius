---
project: bold-synthesis-labeled
audience:
  - Systems / software-engineering program committee members reading a build-infrastructure submission
max_iterations: 4
documents:
  - slug: build-latency-history-problem
    artifact_type: paper
---

# Fixture B — the bold synthesis claim that is not overclaiming

This project is **Fixture B** of the underclaiming / buried-lede regression
pair shipped with `anvil:paper` (issues #1046 → #1047 → #1048). It exists to
prove the other half of #1047's contract: *ambition is not novelty
inflation.* A paper may stake a large synthesis / framing / research-program
claim, in the title and in the first sentence, as long as it labels which
components are inherited, which are demonstrated, which are derived, and
which are conjecture. The reviewer must not score that down as overclaiming.

The body reports the **same measurements from the same trace with the same
bibliography** as its sibling `../underclaiming-buried-lede/` — the
Method-through-Experiments span of the two bodies is byte-identical, and the
two `refs.bib` files are byte-identical — so the 10-point score gap between
the two recorded reviews is attributable to framing alone, not to evidence,
rigor, reproducibility, or citation hygiene.

## Everything here is synthetic

The organization, the three repositories, the 2.1M-invocation trace, every
measurement, and every bibliography entry are **invented for the fixture**.
Nothing in this project reports a real system or a real result, and the
bibliography must not be cited.

## What the recorded review shows

`build-latency-history-problem/build-latency-history-problem.1.review/` is a
recorded `paper-review` pass under the post-#1047 criteria. Its verdict:

- **43/44, `advance: true`** (threshold ≥35), with **zero critical flags**.
- Dim 3 *Clarity of contribution* at full weight (5/5) and dim 9 *Rhetorical
  economy* at full weight (4/4) — the two dimensions #1047 made symmetric.
- **No overclaiming deduction anywhere**, recorded explicitly in
  `_summary.md`'s `overclaiming_check` block and in the dim 3 justification:
  the labeled-ingredients move (`\textbf{Demonstrated}` / `\textbf{Derived}` /
  `\textbf{Synthesis}` / `\textbf{Conjecture}`) is the paper doing its job,
  per `rubric.md` §"Ambition is not novelty inflation".
- The conjecture is stated in falsifiable form and is never presented as a
  result, which is what keeps the bold claim honest rather than inflated.
- The one shared deduction — dim 6 *Figure & table quality* at 3/4 — is
  identical in both fixtures, because both carry the same two tables and no
  rendered figures.

See `../README.md` for the pair's regression contract and
`../../tests/test_paper_underclaiming_fixtures.py` for the assertions.
