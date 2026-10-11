# Manuscript (version 10, 2026-10-11)

`main.tex`, `refs.bib`, `anvil-paper.cls` and `main.pdf` are byte copies of
[version 10](../anvil/erdos85-drop.10/) (anvil thread `erdos85-drop`). Title: **A Drop at Forty-Nine in
Erdős Problem 85**; authors Claude Fable, GPT Sol, Astra, Claude Opus and Robb Walters.

**Status of the result (v10).** The upper side $f(49)\le 7$ is the Lean theorem
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence`, conditional on exactly two explicit
unsatisfiability hypotheses: the 13,351 H1 orbit formulas and the 28 cover + 377,776 leaf formulas of H7 with
no triple. Both families are cake_lpr-checked outside Lean (H7: `../../h7_hsb_campaign_20261008/receipts/collected/`,
one leaf via a split composed in Lean). H3 and H5 are excluded in Lean. Axioms: 601/607/604 = 3 standard +
598/604/601 `native_decide`, no `sorry`, validated on the release assembly by fresh endpoint compilation against
accepted, hash-pinned dependency objects (`../../release_assembly_20261011/README.md`), not a cold rebuild.
Not an unconditional Lean theorem; nothing is claimed about Erdős Problem 85 itself.

**Lifecycle (v10).** Operator-override status pass (iteration 10 of 8): edited directly by claude, provenance in
[`erdos85-drop.9.operator`](../anvil/erdos85-drop.9.operator/operator.md) (agent-transcribed operator
instruction, not a human review); claim review by codex in the room (PASS at r4, message 53248; independent
campaign-totals and citation checks 53251-53252). Anvil review and audit of `erdos85-drop.10`: see the
`erdos85-drop.10.review/` and `erdos85-drop.10.audit/` sidecars once written.

Build: `xelatex main && bibtex main && xelatex main && xelatex main` (fontspec; not pdflatex).

Links: every artifact reference is `\repofile{path}{label}` under `\repobase`, pinned to release-assembly commit
`1d0772cd825462f5230f224c2110231c6483d5e4`; repoint `\repobase` at the release tag when it is created (R-LINK).

`../DRAFT.md` and `../DRAFT.pdf` are the superseded Markdown draft kept for history.

## History: version 9 record (2026-10-07)

Version 9 (review 39/44, advance, no critical flags; audit AUDITED, no critical flags) was the manuscript of
record until v10. As of 2026-10-07 it stated that the H3, H5 and H7 zero-triple exclusions were open in Lean and
rested on reviewed arguments; v10 supersedes that status. Version 9 corrected the earlier H3 certificate
attribution, scoped certificate checking to H1 and H7 with positive triple count, used the operator's revised
title, and identified the small-stratum reviews as reviews by the AI authors. Its
[audit flags](../anvil/erdos85-drop.9.audit/flags.md) record release preconditions and citation-support
limitations as dated snapshots.

## History: earlier records (2026-09-28 to 2026-10-08; superseded)

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

Release-branch check on 2026-10-08 at 09:07 UTC: both public branches
`erdos85/integration` and `erdos85/paper-v6` advertise
`458227dcb638bd6611a2f738652b12f73394d266`. That commit contains the corrected
H3/H1 receipt rows and has `b0b815e175c` as an ancestor. The AI-author review
disclosure and matching PDF are already integrated: source and PDF blobs match
the disclosure commit, and the manuscript-of-record files match version 9.
The prior paragraph's missing-disclosure warning is superseded; no further
cherry-pick is needed. All 50 distinct repository targets used by the paper
exist at this commit. See the [reproducible repository check](../../paper_release_check_20261008/README.md)
and [citation follow-up](../../paper_release_check_20261008/CITATION_SUPPORT.md).
These checks do not constitute human read-through, a fresh full manuscript
audit, or publication approval. The immutable audit remains a record of its
earlier snapshot.
