# Paper release check, 2026-10-08

Repository content check **PASS** at public integration and paper-v6 commit
`458227dcb638bd6611a2f738652b12f73394d266`. This corrects a stale warning in
the manuscript-of-record README; it does not change the paper or its audit.

`REPOSITORY.json` records the exact inspected commit, advertised remote refs,
file hashes, and all 50 distinct targets from 55 repository-link uses.
`check_repository.py` reads Git objects, compares the four record/version files,
checks disclosure-commit ancestry and source/PDF identity, checks the corrected
H3/H1 receipt wording, verifies linked targets, and extracts the shipped PDF
text to check disclosure and unresolved-reference markers. It runs no Lean,
LaTeX, solver, or cloud campaign. Reproduce from a repository checkout with:

```sh
python3 -B research/problems/erdos-85-wip-01/paper_release_check_20261008/check_repository.py \
  --ref 458227dcb638bd6611a2f738652b12f73394d266
```

The command deliberately checks the live branch advertisements against the
specified commit. A later branch advance should fail that snapshot check;
inspect and record the new commit instead of treating the old result as current.

| Requirement | Evidence / remaining work |
|---|---|
| Correct H3/H1 linked receipt (v9 audit P1) | Present on the inspected public commit. |
| AI-author review disclosure | `b0b815e175cbf8b8e46e09028de79c291d98deb3` is an ancestor; both source and PDF match that commit. |
| Record matches v9 | `main.tex`, `main.pdf`, `refs.bib`, `anvil-paper.cls` match byte for byte. |
| Public repository targets | 50/50 exist; Git object IDs retained. Existence does not verify all linked mathematical claims. |
| Current PDF disclosure | Present in the extracted PDF text; no `??`, `[?]`, or `(?)` markers. This is not a fresh compile or visual review. |
| Priority citation claims | See `CITATION_SUPPORT.md`: checker parsing and both hexagon claims supported; both Ramsey intervals follow from cited theorem statements, with the polarity full-proof access limit recorded. |
| Human read-through | No new human approval supplied in this check. |
| Release tag / publication | Not performed. Repoint the paper's repository base only with the chosen release tag in the authorized publication workflow. |

The Anvil paper skill reserves human read-through for the operator: “The
operator's read-through of a `READY` or `AUDITED` thread is the one gate the
lifecycle reserves for a human.” This note is supporting evidence, not a human
verdict or a replacement for the immutable v9 critic directories.

The ongoing H3/H7 formal and certificate work may strengthen a later version.
It is not substituted for the current paper's stated evidence boundary, nor is
global Lean closure imposed here as a new publication requirement.
