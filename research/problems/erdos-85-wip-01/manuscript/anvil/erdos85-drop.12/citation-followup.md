# Citation support follow-up for editable v12

Checked by codex (AI author), 2026-10-11. This is supporting evidence for
the eventual v12 audit, not a completed audit or independent peer review.
Only existing references were retrieved; no literature search, new
bibliography entries, or exhaustive novelty check was performed.

The source identities and retrieval limits are recorded in
`citation-followup-sources.json`. Downloaded publisher/arXiv pages and text
extractions remain in local scratch storage, outside the public repository.
Springer added cookie-error query parameters but returned the expected
paper titles and abstracts, which were inspected locally. The hash records
identify those exact responses, not stable canonical publisher bytes.

| Existing key | Evidence read | Support and limits |
|---|---|---|
| `moura2021lean4` | [Publisher abstract and introduction](https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37) | Supports Lean 4 system attribution. Does not establish this project's compiler version, axiom counts or successful builds. |
| `mathlib2020` | [Author-submitted abstract and DOI cross-reference](https://arxiv.org/abs/1910.09336), plus pinned code below | Supports Mathlib library attribution. Simple-graph usage is verified separately from current pinned code, not inferred from this historical abstract. |
| `wetzler2014drat` | [Publisher abstract](https://link.springer.com/chapter/10.1007/978-3-319-09284-3_31) | Supports the DRAT/drat-trim attribution and proof-checking role. Full subscription chapter was not read. |
| `cruzfilipe2017lrat` | [Publisher abstract](https://link.springer.com/chapter/10.1007/978-3-319-63046-5_14) | Supports LRAT hints and simple certified checking; abstract identifies Coq and ACL2 checkers. Full subscription chapter was not read. |
| `heule2011cube` | [Publisher abstract](https://link.springer.com/chapter/10.1007/978-3-642-34188-5_8) | Supports cube-and-conquer attribution and the partition/solve method. Full subscription chapter was not read. |
| `heule2016pythagorean` | [Publisher abstract](https://link.springer.com/chapter/10.1007/978-3-319-40970-2_15) | Supports large checked combinatorial proofs: reports a verified DRAT proof and a smaller reconstruction certificate. Does not establish that retaining such proofs is impossible. |
| `heule2018schur` | [Publisher abstract](https://ojs.aaai.org/index.php/AAAI/article/view/12209), read through web tool | Reports a constructed and validated proof checked by a formally verified checker. Direct local retrieval failed, so local-source retention remains incomplete. Does not establish a universal inability to keep large proofs. |
| `biere2024cadical2` | [Publisher abstract and introduction](https://link.springer.com/chapter/10.1007/978-3-031-65627-9_7) | Supports CaDiCaL solver attribution. Exact deployed executable identity remains a repository-receipt claim. |

The claim that preceding combinatorial results check proofs “too large to
keep” was stronger than these abstracts establish. The editable draft now
says that large SAT-based results likewise rely on independently checked
proofs. No numerical value or formal trust claim was added.

The two SAT Competition solver-description citations (`biere2024kissat`
and `biere2020cadical`) remain unverified against locally retained source
content. The official [2024 competition page](https://satcompetition.github.io/2024/)
and [2020 downloads page](https://satcompetition.github.io/2020/downloads.html)
link the proceedings, but both institutional repository destinations
([2024](https://helda.helsinki.fi/handle/10138/584822),
[2020](https://helda.helsinki.fi/handle/10138/318450)) returned access-denied
pages during this check. No content verification is inferred from the links.
Earlier limits for Bloom, Zhang and the graph-data page also
remain. The v11 audit is immutable; these notes must be reconciled into a
fresh audit of the final v12 sources.

Pinned-code follow-up: `proofs/lake-manifest.json` pins Mathlib to
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`. The local Mathlib checkout has that
HEAD, and its `Mathlib/Combinatorics/SimpleGraph/Basic.lean` and `Finite.lean`
have no working-tree differences from it. `Basic.lean:92` defines
`SimpleGraph` using symmetric, irreflexive adjacency; `Finite.lean:378`
defines `minDegree`. This project's `Erdos85Problem.lean` imports Mathlib
and uses those definitions in `minDegreeForC4`. This is source inspection,
not a new local Lean build.
