# Manuscript of record (2026-10-07)

Current: `main.tex`, `refs.bib`, `anvil-paper.cls`, and `main.pdf` are byte copies
of [version 9](../anvil/erdos85-drop.9/). Title: **A Drop at Forty-Nine in Erdős
Problem 85**; authors Claude Fable, GPT Sol, Astra, Claude Opus, and Robb Walters.
The version 9 [review](../anvil/erdos85-drop.9.review/verdict.md) records 39/44
and advancement with no critical flags; its [audit](../anvil/erdos85-drop.9.audit/flags.md)
records AUDITED with no critical flags and a clean four-pass XeLaTeX build.
The audit status concerns the manuscript and does not make the computational
upper bound a Lean theorem: the H3, H5, and H7 zero-triple exclusions remain
open in Lean, as disclosed in the paper.

Version 9 corrects the earlier H3 certificate attribution, scopes
certificate checking to H1 and H7 with positive triple count, and uses the
operator's revised title. The current source also identifies the small-stratum
reviews as reviews by the AI authors, not human referees.

## History (2026-09-28 record)

`main.tex`, `refs.bib`, `anvil-paper.cls` and `main.pdf` are byte copies of `../anvil/erdos85-drop.5/`, the version that reached AUDITED in the anvil paper lifecycle (review 38/44, advance, 0 critical flags; audit 0 critical, 0 major, 0 minor, 2 nits). Lifecycle history: v1 17/44 → v2 32/44 → v3 35/44 (audit BLOCK on H7 cell attribution and the five-vs-seven formula count) → v4 37/44 AUDITED → operator read-through rules R-AUD and R-LINK (`../anvil/erdos85-drop/BRIEF.md`) → v5 38/44 AUDITED.

Build: `xelatex main && bibtex main && xelatex main && xelatex main` (fontspec; not pdflatex).

Links: every artifact reference is `\repofile{path}{label}` under `\repobase` = `https://github.com/rjwalters/lean-genius/blob/erdos85/integration`; repoint `\repobase` at the release tag when it is created.

`../DRAFT.md` and `../DRAFT.pdf` are the superseded Markdown draft kept for history.

Before publication, use the version 9 [audit flags](../anvil/erdos85-drop.9.audit/flags.md)
for the recorded release preconditions, citation-support limitations, and
remaining minor findings. Its repository-state observations are dated snapshots:
verify that the corrected receipts and paper are on the release branch before
creating a release tag and repointing `\repobase`. The older
[wrap-up punchlist](../../WRAPUP_PUNCHLIST_20260921.md) remains historical context;
its version 5/8 wording notes are superseded where version 9 addresses them.

Release-branch check on 2026-10-08: fetched `erdos85/integration` at
`bc5291aa220` already contains the corrected H3/H1 receipt rows identified by
the audit's P1 note. It does not yet contain `b0b815e175c`, which adds the
AI-author review disclosure to the abstract and collaboration section. Include
that disclosure, its matching PDF, and this README correction in the release
branch before publishing; the immutable audit remains a record of its earlier
snapshot.
