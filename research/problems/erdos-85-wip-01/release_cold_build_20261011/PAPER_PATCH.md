# Proposed review fixes for the next paper version

`paper-review-fixes.patch` applies to a new draft copied from v11. It does
not change the immutable v11, the manuscript of record, or the cold-build
execution sources. It is a partial editing proposal, not a frozen v12 or
an Anvil review/audit result. Codex prepared it as an AI author.

The six substitutions address v11 review m1 and n1/n2/n3/n5: position H7
against the verified symmetry breaking in the empty-hexagon development;
remove two stale “now” phrases; qualify the H1 cost as controller estimates
and link both receipts; use “previously known”; and state H5's 18 cover and
cardinality checks. The H7 wording expressly describes composition of cover
and leaf UNSAT hypotheses, preserving cover UNSAT as an unproved hypothesis.
Its source anchors are HsbSound.lean lines 434–487, HsbLeaves.lean lines
99–143, and sections 5–6 of the retained Subercaseaux et al. primary paper.
The cost receipts report approximately $204 (including a 10% margin) and
$20, so the manuscript's approximate $225 remains an estimate.

Apply only in a new, editable draft directory containing the v11 main.tex:

```sh
patch -p1 --directory /path/to/new/draft --input /absolute/path/to/paper-review-fixes.patch
```

The input source SHA256, output source SHA256 and patch SHA256 are recorded
in `paper-review-fixes-check.json`. Actual patch application in a scratch
copy reproduced the proposed source byte for byte. Three XeLaTeX passes
with BibTeX converged to an aux fixpoint: 14 pages, zero overfull boxes,
no undefined citations/references or rerun warnings. The two added artifact
links exist at the current paper pin. The raw build output is retained in
`paper-review-fixes-compile.log`; the scratch PDF is not the released paper.

Still to resolve in the final revision: publication/cold-build status and
artifact pin, the status-table availability wording, the stale BRIEF and
manuscript README, and the linked H7 README's operator-ceiling clause. The
main-text length advisory remains. The final combined revision requires its
own render, link, numeric, claim, review and audit checks; this scratch build
does not establish those results in advance.
