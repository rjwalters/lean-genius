# Worked fixtures — underclaiming vs. bold synthesis

Two hand-authored `anvil:paper` projects that report **the same synthetic
study, with the same evidence and the same bibliography, framed two ways**.
They are the regression fixtures for the dim 3 / dim 9 symmetry shipped in
issue #1047 (`rubric.md` §"Dim 3 / Dim 9 — overclaiming and underclaiming are
symmetric failure modes" and §"Ambition is not novelty inflation";
`commands/paper-review.md` §"Underclaiming / buried-lede finding").

| Fixture | Project | Framing | Recorded review |
|---|---|---|---|
| **A** | `underclaiming-buried-lede/` | Rigorous, hedged, organizing idea demoted to the last paragraph of the Discussion | **33/44**, `advance: false`, named `underclaiming_buried_lede` finding at `blocker` severity |
| **B** | `bold-synthesis-labeled/` | Synthesis claim in the title and first sentence, each contribution labelled demonstrated / derived / synthesis / conjecture | **43/44**, `advance: true`, **no** overclaiming deduction |

Issue #1046 asked for exactly this pair: *"at least one fixture proves that a
safe, polished, boring paper can fail review"* and *"at least one fixture
proves that an ambitious paper can pass without claiming that all of its
ingredients are new."*

## The regression contract

The load-bearing property is not either score on its own — it is that the two
fixtures **hold their evidence constant and vary only their framing**:

- The `\section{Method}`-through-`\section{Experiments}` span of the two
  `main.tex` bodies is **byte-identical**.
- The two `refs.bib` files are **byte-identical**.
- The `## Strongest claim` section of the two thread briefs is
  **byte-identical** — both drafts were briefed on the same organizing idea,
  which is what makes "the paper does not match its own brief" a checkable
  statement for Fixture A.
- The two recorded reviews therefore score **identically** on dims 1, 2, 5, 6,
  and 8 (6, 6, 5, 3, 5) — rigor, evidence sufficiency, reproducibility,
  figure/table quality, citation hygiene.
- The entire 10-point gap sits in dims **3, 4, 7, and 9**.

`../tests/test_paper_underclaiming_fixtures.py` pins all of it. If a future
rubric or command-doc edit makes caution cheap again (Fixture A creeping to
≥35) or makes ambition costly (Fixture B dropping below 35, or acquiring an
overclaiming deduction), the test fails and names which half of the contract
broke.

## Everything here is synthetic

The organization, the three repositories, the 2.1M-invocation trace, every
measurement, and every bibliography entry are **invented for these fixtures**.
The bibliography entries are complete and internally consistent so the
fixtures exercise dim 8 honestly — not so they can be cited. **Do not cite
them.** The numbers are mutually consistent (text against tables, ablation
against the deployment claim) because a fixture that contradicted itself would
trip a critical flag for the wrong reason.

## Structure

```
examples/
  README.md                                   this file
  underclaiming-buried-lede/                  Fixture A — project root
    BRIEF.md                                  project brief (project + documents:
                                              [{slug, artifact_type: paper}])
    build-cache-miss-study/                   thread dir (named for the slug)
      BRIEF.md                                thread brief incl. the six-question
                                              `## Strongest claim` inventory
                                              (paper-draft.md §"Strongest-claim
                                              inventory")
      build-cache-miss-study.1/               the drafted version (terminal here)
        main.tex                              LaTeX body
        refs.bib                              synthetic bibliography
        _progress.json                        { version: 1, phases.draft.state: "done",
                                                metadata.opening_leads_with_strongest_claim:
                                                false }
      build-cache-miss-study.1.review/        reviewer sibling
        verdict.md                            33/44, advance: false, the cold-reader
                                              table, zero critical flags
        scoring.md                            9-row table with quoted evidence per dim
        comments.md                           the named blocker-severity finding
        findings.md                           cross-section observations
        _summary.md                           machine-readable scores +
                                              underclaiming_check + overclaiming_check
        _meta.json                            human-verdict + anvil-pub-v2 / 44 / 35
        _progress.json                        { for_version: 1, phases.review.state: "done" }
  bold-synthesis-labeled/                     Fixture B — same shape
    BRIEF.md
    build-latency-history-problem/
      BRIEF.md
      build-latency-history-problem.1/{main.tex, refs.bib, _progress.json}
      build-latency-history-problem.1.review/{verdict,scoring,comments,findings}.md
                                              + _summary.md + _meta.json + _progress.json
```

Following the `essay` / `memoir` / `spec` worked examples, the vendored review
siblings carry the prose manifest plus `_summary.md` and omit `_review.json` —
the canonical critic JSON is written by a live `paper-review` run, and no
shipped anvil example vendors one.

Both threads are deliberately terminal at version 1 with a single `.review/`
sibling and no `.audit/`: the pair exists to compare **two first drafts under
one rubric**, not to demonstrate a revise loop or an audit pass. There is no
`expected-thread.N/` companion directory here for the same reason — the
sibling skills use one to describe a *realized* thread's structural contract,
whereas these fixtures are hand-authored inputs to a test that pins the
contract directly.

## Provenance of the scores (read this before trusting them)

The two `.review/` siblings are **recorded reviewer passes**, not deterministic
computations. They were produced by applying `commands/paper-review.md` step 5
and `rubric.md` to the two bodies by hand, at the time the fixtures were
written (issue #1048), and then frozen. This is the same posture the
`essay` / `primer` / `spec` worked examples take toward their vendored
reviews, and the same tension `paper-audit`'s vision-owned dimensions
navigate: the numbers are judgment, so the test pins **the recorded judgment
and its structure**, not a re-derivation.

What that buys, and what it does not:

- **Regression-checkable**: the recorded scores, the named finding, the
  evidence-dim parity, and the shared-span invariant are all mechanically
  asserted. A change that would make either fixture score differently under a
  fresh review is *detectable* only if someone re-runs the review; a change
  that alters the fixtures themselves is caught immediately.
- **Not a golden re-run**: re-running `paper-review` against these bodies on a
  different model may land a point or two away from 33 and 43. That is
  expected. What must not change is the *shape*: Fixture A below 35 with the
  named finding and full marks on rigor/evidence/citation hygiene, Fixture B
  at or above 35 with no overclaiming deduction. The test asserts the shape
  with explicit tolerance where the shape allows it (see its
  `test_recorded_totals_*` docstrings).

Every dimension justification in both `scoring.md` files quotes the body
verbatim and is verified by `anvil/lib/evidence_check.py` in the test — so the
recorded judgment is at least anchored to text that actually exists.

## Using these fixtures

- **As a reviewer calibration reference**: read Fixture A's `verdict.md`
  cold-reader table next to Fixture B's ambition-versus-inflation table. They
  are the two halves of the same check.
- **As a drafting reference**: Fixture B's `main.tex` §1 shows the labelled
  contribution list (`\textbf{Demonstrated}` / `\textbf{Derived}` /
  `\textbf{Synthesis}` / `\textbf{Conjecture}`) that `paper-draft.md`
  §"Strongest-claim inventory" asks for, and Fixture A's shows what a draft
  looks like when it silently answers question 5 in the negative.
- **Not as a template**: `assets/example-brief.md` remains the smoke-test
  brief for drafting. These are diagnostic fixtures.
