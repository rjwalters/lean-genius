# Citation audit: erdos85-drop.10

**Scope.** Every `\cite`, `\citep` and `\citet` in `erdos85-drop.10/main.tex`. The paper is a single file with no `\input` or `\include`. Each key was resolved against `erdos85-drop.10/refs.bib` and against the rendered bibliography of a fresh xelatex/bibtex compile at the `.aux` fixpoint.

**Claim-support sources.** `erdos85-drop/refs/**`. No PDF of any cited work is on disk. The author notes are `FIRST_DROP_LITERATURE_CHECK.md`, `DRAFT.md` and `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`. Web search is off (BRIEF `web_search: false`), so nothing was re-fetched. Codex reports spot-checks against primary sources for cake_lpr, the hexagon papers and the Zhang/Boza bounds (`erdos85-drop.10.independent/README.md`, room 53252). Those checks are not on disk, so they are recorded here as corroboration and do not change any verdict.

## Resolution summary

- 17 distinct keys and 23 key occurrences. All 17 resolve in `refs.bib`, which has 17 entries and none unused.
- BibTeX: 0 warnings. Final xelatex pass: 0 `Citation ... undefined`. `pdftotext` of the fixpoint PDF finds 0 `??`, 0 `[?]` and 0 `(?)`.
- `refs.bib` is byte-identical to v9. The multiset of cite commands is identical to v9: v10 adds and removes no citation.
- Correction to the v9 audit: that audit reported 16 keys and left out `biere2024cadical2`, which v9 already cited (L147 here). The count was wrong, but no verdict changes.
- 0 unresolved keys and 0 `does-not-support` verdicts, so this file raises no critical flag.

## Per-citation table

| Key | Resolved | Surrounding claim (main.tex line) | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | L73: problem statement. L85: the maintained record lists no partial result and warns that its literature list may be incomplete | partial | `FIRST_DROP_LITERATURE_CHECK.md` §1. The live page was not re-read (web off). |
| `moura2021lean4` | yes | L73 "In Lean 4" | unverified (source not on disk) | System citation. |
| `mathlib2020` | yes | L73 "on Mathlib's simple graphs" | unverified (source not on disk) | System citation. |
| `boza2024ramsey` | yes | L75: r(s)=R(C4,K_{1,s}), r(41)=49, r(42)∈{49,50}. L85: no consecutive equality yields a drop. L257: r(109), r(155) | partial | `FIRST_DROP_LITERATURE_CHECK.md` §2. The r-to-f conversion was re-derived by hand and is correct (r(42)=49 ⇔ f(49)≤7). |
| `zhang2017polarity` | yes | L75 (co-cited for the convention); L257 r(109)∈{120,121}, r(155)∈{168,169} | partial | Author note only. Codex reports a primary-source check (off disk). |
| `afzaly-mckay-extremal` | yes | L93: non-isomorphic to the ten 48-vertex, 168-edge graphs; the 49-vertex records corroborate only f(49)≥7 | partial | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt` PASS. |
| `biere2024kissat` | yes | L147 "Kissat 4.0.4" | unverified (source not on disk) | Conventional. |
| `biere2020cadical` | yes | L147 "CaDiCaL 3.0.1" | unverified (source not on disk) | Co-cited with `biere2024cadical2`. The first mention of CaDiCaL 3.0.1 (L132, H7) is uncited (nit N2). |
| `biere2024cadical2` | yes | L147 (co-cited) | unverified (source not on disk) | CAV 2024, DOI present. |
| `wetzler2014drat` | yes | L151: DRAT proofs are checked by drat-trim | unverified (source not on disk) | Standard attribution. |
| `cruzfilipe2017lrat` | yes | L151: LRAT adds hints for a small checker | unverified (source not on disk) | Standard attribution. |
| `tan2021cakelpr` | yes | L151: cake_lpr correctness, including file parsing, proved in HOL4 and compiled by the verified CakeML compiler | unverified (source not on disk) | Matches BRIEF R-CERT. DOI now present (`10.1007/978-3-030-72013-1_12`), so review n5 is stale for this key. |
| `heule2016pythagorean` | yes | L151: large SAT results check proofs too large to keep | unverified (source not on disk) | Standard. |
| `heule2018schur` | yes | L151 (co-cited) | unverified (source not on disk) | DOI now present (`10.1609/aaai.v32i1.12209`), so review n5 is stale here too. |
| `heule2024hexagon` | yes | L85, L153: 30 points in general position contain an empty convex hexagon; cube-and-conquer; proof checked by cake_lpr | partial | Crossref abstract read in the v8 audit. The sentence is unchanged in substance. |
| `subercaseaux2024hexagonlean` | yes | L85, L153: Lean verification of encoding faithfulness, joined to the cake_lpr check; "The hexagon verification and ours both reduce … in Lean … and both rely on cake_lpr" | partial | DataCite abstract read in the v8 audit. The v10 addition ("both rely on cake_lpr"; "23 for H1, 598 for the whole upper side") concerns our side only and matches `H1_COVER_AXIOMS_20261006.txt` and `RELEASE_ASSEMBLY_README_20261011.md`. |
| `heule2011cube` | yes | L153 cube-and-conquer | unverified (source not on disk) | Standard attribution. |

**Totals.** 0 supports, 6 partial, 11 unverified, 0 does-not-support.

## Non-`\cite` provenance links (R-LINK), checked here because they carry claims

- 69 `\repofile`/`\repofiletab` uses resolve to 63 distinct targets. All 63 exist at the pinned commit `1d0772cd825462f5230f224c2110231c6483d5e4`, checked with `git cat-file -e`. That commit is an ancestor of `origin/erdos85/release-assembly-20261011`, and `git ls-remote` shows the remote head at `98ee2fc33428`. Codex counted 63 as well; the review's 64 was probably an off-by-one.
- **Claim-support failure of a linked receipt (see flags.md C2).** L132 attaches "about \$215 of cloud compute" to `h7_hsb_campaign_20261008/receipts/collected/campaign_totals.json`. That file, at the pin and in `refs/h7_campaign_totals_20261011.json` (byte-identical), has no cost field.
- **Stale linked receipt (flags.md M2).** At the pin, `STRATA_AND_SMALL_ORDERS_20260928.md` contradicts the paper on H3, H5 and H7.
