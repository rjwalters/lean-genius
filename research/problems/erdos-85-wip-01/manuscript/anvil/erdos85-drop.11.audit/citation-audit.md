# Citation audit: erdos85-drop.11

Auditor: codex, an AI author of this paper. This is an author audit, not an independent external review. Source-support checks below combine the v10 audit's retained notes with primary materials read during finalization. PDFs remain in scratch storage; URLs, byte counts and SHA256 identities are in `citation-source-manifest.json`. The preprints checked are identified by version; this does not assert identity to publisher versions.

All 17 distinct keys (25 occurrences) resolve against the 17 bibliography entries, with none unused. There are no input/include children. BibTeX and the final XeLaTeX pass have no unresolved citations, and the rebuilt PDF has no unresolved-reference markers. The bibliography is unchanged from v10; v11 adds the two CaDiCaL keys at the first H7 mention.

| Key | Resolved | Surrounding claim | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | Problem statement; qualified first-drop claim and maintained record | partial | Retained `FIRST_DROP_LITERATURE_CHECK.md`; live page retrieval returned 403. No fresh verification of its current state or exhaustive novelty search is claimed. |
| `moura2021lean4` | yes | Lean 4 system attribution | unverified — source not on disk | Conventional system citation; carried from v10. |
| `mathlib2020` | yes | Mathlib simple graphs | unverified — source not on disk | Conventional system citation; carried from v10. |
| `boza2024ramsey` | yes | Ramsey convention, r(41)=49, r(42) in {49,50}, finite table and later bounds | supports | [arXiv v2](https://arxiv.org/pdf/2409.12770v2), p.4 table visually inspected; Corollaries 3 and 7 read. The conversion to this paper's f is algebraic. |
| `zhang2017polarity` | yes | Ramsey convention and bounds used at q=11,13 | partial | Full paper unavailable locally. [Primary institutional abstract](https://research.polyu.edu.hk/en/publications/polarity-graphs-and-ramsey-numbers-for-csub4subversus-stars/) was read through the web tool; direct download returned 403. Formula at t=1 gives r(120)=132 and r(168)=182. Combining Boza's Corollaries 7 and 3 gives the stated intervals for r(109), r(155). This checks the stated result, not its proof. |
| `afzaly-mckay-extremal` | yes | Ten order-48 graphs and order-49 lower-side records | partial | [Primary data page](https://users.cecs.anu.edu.au/~bdm/data/extremal.html) and legend read: entries are lower bounds, not maximality claims. Nonisomorphism/degree details rely on retained `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, not a new census run. |
| `biere2024kissat` | yes | Kissat attribution | unverified — source not on disk | Executable version/hash claims come from repository receipts, not this system paper. |
| `biere2020cadical` | yes | CaDiCaL attribution, H7 and H1 | unverified — source not on disk | Co-cited with CaDiCaL 2.0; exact deployed binary is pinned separately. |
| `biere2024cadical2` | yes | CaDiCaL attribution | unverified — source not on disk | DOI resolves syntactically in bibliography; no new publisher-content verification. |
| `wetzler2014drat` | yes | DRAT/drat-trim attribution | unverified — source not on disk | Retained v10 limitation. |
| `cruzfilipe2017lrat` | yes | LRAT hints and small checkers | unverified — source not on disk | Retained v10 limitation. |
| `tan2021cakelpr` | yes | HOL4/CakeML checker correctness, including parsing | supports | [Author-hosted paper](https://cakeml.org/tacas21.pdf), §4.1 (PDF p.9): source-level parsing/IO correctness composed with verified compilation supports the stated guarantee. No Lean-kernel guarantee is inferred. |
| `heule2016pythagorean` | yes | Large checked SAT proofs | unverified — source not on disk | Retained v10 limitation. |
| `heule2018schur` | yes | Large checked SAT proofs | unverified — source not on disk | Retained v10 limitation; DOI already present. |
| `heule2024hexagon` | yes | Empty hexagon at 30 points, cube-and-conquer and cake_lpr | supports | [arXiv v1](https://arxiv.org/pdf/2403.00737v1), theorem and §7.1/7.3: concurrent LRAT checking and cube-cover checking support the method comparison. |
| `subercaseaux2024hexagonlean` | yes | Lean encoding-faithfulness proof joined to external cake_lpr checks | supports | [arXiv v1](https://arxiv.org/pdf/2403.17370v1), §7 explicitly describes external checking and the UNSAT axiom used by Lean. The manuscript claims no advantage on this trust axis. |
| `heule2011cube` | yes | Cube-and-conquer attribution | unverified — source not on disk | Retained v10 limitation. |

Totals: **4 supports, 3 partial, 10 unverified, 0 does-not-support, 0 unresolved keys**. Unverified source support is an explicit audit limitation, not a fabricated pass.

All 70 repository-link uses expand through `repofile`/`repofiletab` to 64 distinct paths present at pinned commit `f6daa149b807972abe1c3e669abce092a863c2bd`; `build-check.json` lists them. Macro definitions expand to public GitHub hrefs. The previous unsourced H7 dollar claim is deleted. The historical STRATA note now carries an explicit superseded-status banner at the pin. These resolve v10 C2 and M2. Git object existence was checked for every target; this is not a claim that every URL was fetched over HTTP during this audit.
