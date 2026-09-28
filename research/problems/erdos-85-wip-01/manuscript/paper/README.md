# Manuscript of record (2026-09-28)

`main.tex`, `refs.bib`, `anvil-paper.cls` and `main.pdf` are byte copies of `../anvil/erdos85-drop.5/`, the version that reached AUDITED in the anvil paper lifecycle (review 38/44, advance, 0 critical flags; audit 0 critical, 0 major, 0 minor, 2 nits). Lifecycle history: v1 17/44 → v2 32/44 → v3 35/44 (audit BLOCK on H7 cell attribution and the five-vs-seven formula count) → v4 37/44 AUDITED → operator read-through rules R-AUD and R-LINK (`../anvil/erdos85-drop/BRIEF.md`) → v5 38/44 AUDITED.

Build: `xelatex main && bibtex main && xelatex main && xelatex main` (fontspec; not pdflatex).

Links: every artifact reference is `\repofile{path}{label}` under `\repobase` = `https://github.com/rjwalters/lean-genius/blob/erdos85/integration`; repoint `\repobase` at the release tag when it is created.

`../DRAFT.md` and `../DRAFT.pdf` are the superseded Markdown draft kept for history.

Open before publication (see `../../WRAPUP_PUNCHLIST_20260921.md`): the operator's read-through; the two audit nits (§3.1 `Lean.ofReduceBool` identification is a statement about Lean's implementation, not printed by `axioms.out`; Appendix B "thirteen input hashes" is the 2026-08 grid campaign's inputs, not the thirteen H7 certificate modules); the abstract no longer mentions `native_decide` for the lower sides (still disclosed in §1, Table 1, §4.1, §6); the nine citations with no source on disk (author obligation: check Zhang–Chen–Cheng's values and Boza's r(109), r(155) bounds against the papers); a figure and a method-lineage literature search were declined for lack of sources.
