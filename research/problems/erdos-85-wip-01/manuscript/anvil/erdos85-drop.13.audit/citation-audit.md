# Citation audit: erdos85-drop.13

Auditor: Claude (Opus 5.5) acting as the anvil paper-audit critic. Claude models are listed AI authors of the paper, so this is not an independent external review.

`erdos85-drop.13/refs.bib` is byte-identical to `erdos85-drop.12/refs.bib` (`diff`). `main.tex` changes from v12 touch no `\cite`/`\citep`/`\citet` sentence (full diff read: the `\repocommit` macro, the date, and the L95, L113, L134, L193, Table 2, L238, L274 and L282 wording). There are no `\input`/`\include` children. All 17 distinct keys resolve and none is unused. BibTeX exits 0. The converged XeLaTeX pass has 0 undefined citations, and the rebuilt PDF text has no `??`.

No `refs/` source PDF exists for any bibliography key. Since neither the cited sentences nor the bibliography changed, the v12 verdicts carry forward unchanged. The basis for each is in `erdos85-drop.12.audit/citation-audit.md`, which records which verdicts rest on full-text reads and which on abstract-level reads. No source was re-read for v13.

| Key | Resolved | Surrounding claim | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | Problem statement; qualified first-drop claim | partial | carried from v12 |
| `moura2021lean4` | yes | Lean 4 attribution | partial (abstract-level) | carried |
| `mathlib2020` | yes | Mathlib simple graphs | partial (abstract-level) | carried |
| `boza2024ramsey` | yes | r(s) convention; r(41)=49; r(42) in {49,50}; intervals | supports | carried |
| `zhang2017polarity` | yes | convention; values for r(109), r(155) | partial | carried |
| `afzaly-mckay-extremal` | yes | ten 48-vertex/168-edge graphs; 49-vertex min-degree-6 records | partial | carried |
| `biere2024kissat` | yes | Kissat attribution | unverified — source not on disk | carried |
| `biere2020cadical` | yes | CaDiCaL attribution | unverified — source not on disk | carried |
| `biere2024cadical2` | yes | CaDiCaL attribution | partial (abstract-level) | carried |
| `wetzler2014drat` | yes | DRAT / drat-trim | partial (abstract-level) | carried |
| `cruzfilipe2017lrat` | yes | LRAT hints | partial (abstract-level) | carried |
| `tan2021cakelpr` | yes | cake_lpr verified incl. parsing, HOL4/CakeML | supports | carried |
| `heule2016pythagorean` | yes | large SAT results rely on independently checked proofs | partial (abstract-level) | carried |
| `heule2018schur` | yes | same sentence | partial (abstract-level) | carried |
| `heule2024hexagon` | yes | 30 points, empty hexagon, cube-and-conquer, cake_lpr | supports | carried |
| `subercaseaux2024hexagonlean` | yes | Lean encoding faithfulness; verified symmetry breaking | supports | carried (v12 re-read arXiv 2403.17370v1 §5) |
| `heule2011cube` | yes | cube-and-conquer attribution | partial (abstract-level) | carried |

Totals: **4 supports, 11 partial (8 abstract-level), 2 unverified, 0 does-not-support, 0 unresolved.**

## Repository links (R-LINK) and the commit of record

- `\repocommit` = `2029149d7e42b74036ff0e1e82af6d33c2e32748`. `\repobase` = `https://github.com/rjwalters/lean-genius/blob/\repocommit`. The Availability prose (L274) prints `\texttt{\repocommitshort}` = `2029149d7e42`, which is the first 12 characters of `\repocommit`. **The displayed commit matches the link pin (v12 C1 resolved).**
- The 80 `\repofile`/`\repofiletab` uses expand to 70 distinct paths, and `git cat-file -e 2029149d7e42:<path>` succeeds for **70/70**.
- In the compiled PDF's link annotations (stream-decoded), all 82 `github.com/rjwalters/lean-genius/blob/...` URIs use the full pin hash. No other blob hash appears.
- `git ls-remote origin refs/heads/erdos85/release-assembly-20261011` returns `2029149d7e42...`, so the pin is the published branch head. An unauthenticated GET of the `ACCEPTED.md` blob URL at the pin returned HTTP 200, and the raw file at the pin contains the "squad review #2749" re-audit paragraph.
- The pin is a single commit on top of the v12 pin `fa2b41268df`. It changes only six record or script files (`fetch-h7-certificates.sh`, plus cold-build `ACCEPTED.md`/`FAILURE.md`/`README.md` and third-party `ACCEPTED.md`/`THIRDPARTY.md`), and makes no Lean source change. `proofs/Proofs` at the pin is identical to the build execution commit `afa46bc5078`.
