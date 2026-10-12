# Citation audit: erdos85-drop.12

Auditor: Claude (Opus 5.5) acting as the anvil paper-audit critic. The paper lists Claude Fable and Claude Opus as AI authors, so this is not an independent external review. No `refs/` source PDF exists for any bibliography key; verdicts below come from (a) the v11 audit's retained primary-source reads (`erdos85-drop.11.audit/citation-source-manifest.json`), (b) the author follow-up `erdos85-drop.12/citation-followup.md` (abstract-level reads by codex, not re-read here), and (c) one primary source re-read in this audit. Nothing is marked `supports` without a full-text read by an auditor.

All 17 distinct keys resolve against the 17 entries of `erdos85-drop.12/refs.bib`, and none is unused. `refs.bib` is byte-identical to v11 (`cmp`). There are no `\input`/`\include` children. BibTeX reports 0 warnings. The final XeLaTeX pass has no undefined citations, and the rebuilt PDF text has no `??`.

| Key | Resolved | Surrounding claim | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | Problem statement; qualified first-drop claim; record lists no partial result | partial | Carried from v11: retained `FIRST_DROP_LITERATURE_CHECK.md`; live page not re-fetched. Novelty stays qualified ("to our knowledge"). |
| `moura2021lean4` | yes | Lean 4 attribution | partial (abstract-level) | Author follow-up read the publisher abstract and introduction. Attribution only. |
| `mathlib2020` | yes | Mathlib simple graphs | partial (abstract-level) | Author follow-up: arXiv abstract plus source inspection of pinned Mathlib `SimpleGraph`/`minDegree`. Attribution only. |
| `boza2024ramsey` | yes | Convention r(s)=R(C4,K_{1,s}); r(41)=49; r(42) in {49,50}; later intervals | supports | Carried from v11 (arXiv v2 p.4 table; Corollaries 3, 7). |
| `zhang2017polarity` | yes | Convention; values used for r(109), r(155) | partial | Carried from v11: abstract only. |
| `afzaly-mckay-extremal` | yes | Ten 48-vertex/168-edge graphs; 49-vertex min-degree-6 records | partial | Carried from v11: data page and legend; nonisomorphism relies on the repository receipt. |
| `biere2024kissat` | yes | Kissat attribution | unverified — source not on disk | Follow-up: repository pages returned access-denied. |
| `biere2020cadical` | yes | CaDiCaL attribution | unverified — source not on disk | Same as above. |
| `biere2024cadical2` | yes | CaDiCaL attribution | partial (abstract-level) | Author follow-up: publisher abstract and introduction. |
| `wetzler2014drat` | yes | DRAT / drat-trim | partial (abstract-level) | Author follow-up: publisher abstract. |
| `cruzfilipe2017lrat` | yes | LRAT hints, small checker | partial (abstract-level) | Author follow-up: publisher abstract. |
| `tan2021cakelpr` | yes | cake_lpr correctness including parsing, HOL4/CakeML | supports | Carried from v11 (§4.1 of the author-hosted paper). |
| `heule2016pythagorean` | yes | "Large SAT-based results ... rely on independently checked proofs" (v12 rewording) | partial (abstract-level) | Follow-up: the abstract reports a verified DRAT proof. The v12 rewording removed the unsupported "too large to keep" claim. The weaker claim is consistent with the abstract. |
| `heule2018schur` | yes | Same sentence | partial (abstract-level) | Follow-up: the abstract reports validation by a formally verified checker. Consistent with the reworded claim. |
| `heule2024hexagon` | yes | 30 points, empty hexagon, cube-and-conquer, cake_lpr | supports | Carried from v11 (arXiv v1). |
| `subercaseaux2024hexagonlean` | yes | (v11) Lean faithfulness of encoding joined to cake_lpr; (v12, new) "verified symmetry breaking in the empty-hexagon development" | supports | Re-read in this audit: arXiv 2403.17370v1, sha256 `281accaa497ac22376218abb8161e10184f60590f862ba7597560457f3aff72e`. Section 5 "Symmetry Breaking" states a Lean `theorem symmetry_breaking` and proves it. The paper also says that 34% of the development "validates the symmetry breaking and SAT encoding". This supports the new v12 sentence. The PDF was downloaded to scratch and not retained in `refs/`. |
| `heule2011cube` | yes | Cube-and-conquer attribution | partial (abstract-level) | Author follow-up: publisher abstract. |

Totals: **4 supports, 11 partial (8 of them abstract-level only), 2 unverified, 0 does-not-support, 0 unresolved keys.** The 8 abstract-level verdicts rest on the author's follow-up record and were not re-read here. Abstract-level support is enough for attribution citations. It is not a full-text verification.

## Repository links (R-LINK)

The 80 `\repofile`/`\repofiletab` uses expand to 70 distinct paths under `\repobase` = `blob/fa2b41268df024128ed4738b3bb500637cf1ec12`. Each was checked with `git cat-file -e fa2b41268df:<path>`: **70/70 exist.** `git ls-remote origin` shows `fa2b41268df` as the head of `erdos85/release-assembly-20261011` and `erdos85/release-thirdparty-rebuild-20261012`. An unauthenticated HTTPS GET of the third-party `ACCEPTED.md` blob URL returned 200. Other URLs were not fetched one by one.

The Availability prose names a **different** commit (`92ff6248033c`). See flags.md C1.
