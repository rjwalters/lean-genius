# Citation audit: erdos85-drop.9

**Scope.** Every `\cite`, `\citep` and `\citet` in `erdos85-drop.9/main.tex` (single file; no `\input`/`\include`), resolved against `erdos85-drop.9/refs.bib` and against the rendered bibliography of a fresh xelatex/bibtex compile at the `.aux` fixpoint.

**Claim-support sources.** `erdos85-drop/refs/**` (no PDF of any cited work is on disk; author notes `FIRST_DROP_LITERATURE_CHECK.md`, `DRAFT.md`, `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`). For the two hexagon keys, the DOI-resolver abstracts read by the v8 audit (Crossref `10.1007/978-3-031-57246-3_5`, DataCite `10.4230/LIPIcs.ITP.2024.35`); not re-fetched this run (web off; the cited sentences are unchanged in substance except the m1 antecedent fix). No new source was consulted.

## Resolution summary

- 16 distinct keys, 22 occurrences; 16/16 resolve in `refs.bib` (16 entries, none unused).
- BibTeX: 0 `Warning--` lines.
- Final xelatex pass: 0 `Citation ... undefined`; `pdftotext` of the fixpoint PDF: 0 `??`, 0 `[?]`, 0 `(?)`.
- `erdos85-drop.9/refs.bib` vs thread-root `erdos85-drop/refs.bib`: same 16 keys; differences are formatting only (`year = {n.d.}`, brace protection, notes, entry layout).
- 0 unresolved keys, 0 `does-not-support` verdicts -> no critical flag from this file.

## Per-citation table

| Key | Resolved | Surrounding claim (main.tex line) | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | L73 problem statement; L85 "the maintained record lists no partial result and warns that its literature list may be incomplete" | partial | `FIRST_DROP_LITERATURE_CHECK.md` §1 (checked 2026-08-25). Live page not re-read (web off). |
| `moura2021lean4` | yes | L73 "In Lean 4" | unverified (source not on disk) | System citation. |
| `mathlib2020` | yes | L73 "on Mathlib's simple graphs" | unverified (source not on disk) | System citation. |
| `boza2024ramsey` | yes | L75 r(s)=R(C4,K_{1,s}); r(41)=49, r(42)∈{49,50}; L85 no consecutive equality yields a drop; L239 r(109), r(155) bounds | partial | `FIRST_DROP_LITERATURE_CHECK.md` §2; `DRAFT.md` deductions. r-to-f conversion re-derived by hand: correct. |
| `zhang2017polarity` | yes | L75 co-cited for the convention; L239 r(109)∈{120,121}, r(155)∈{168,169} | partial | Author note only (`DRAFT.md`); bound itself unverified on disk. Carried author obligation. |
| `afzaly-mckay-extremal` | yes | L93 non-isomorphic to the ten 48-vertex 168-edge graphs; 49-vertex records corroborate f(49)≥7 only | partial | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt` PASS (10 archive graphs); lower-bound labelling per `FIRST_DROP_LITERATURE_CHECK.md`. |
| `biere2024kissat` | yes | L131 "Kissat 4.0.4" | unverified (source not on disk) | Competition description for a later release; conventional. |
| `biere2020cadical` | yes | L131 "CaDiCaL 3.0.1" | unverified (source not on disk) | 2020 description cited for 3.0.1 (carried nit). |
| `wetzler2014drat` | yes | L135 DRAT proofs checked by drat-trim | unverified (source not on disk) | Standard attribution. |
| `cruzfilipe2017lrat` | yes | L135 LRAT adds hints for a small checker | unverified (source not on disk) | Standard attribution. |
| `tan2021cakelpr` | yes | L135 cake_lpr correctness incl. parsing proved in HOL4, compiled by verified CakeML | unverified (source not on disk) | Matches BRIEF R-CERT wording; author should confirm the parsing claim against the TACAS paper. |
| `heule2016pythagorean` | yes | L135 large SAT results check proofs too large to keep | unverified (source not on disk) | Standard. |
| `heule2018schur` | yes | L135 (co-cited) | unverified (source not on disk) | No DOI (carried nit). |
| `heule2024hexagon` | yes | L137 30 points in general position contain an empty convex hexagon; cube-and-conquer; proof checked by cake_lpr | partial | Crossref abstract (read in v8 audit) supports the result and cube-and-conquer; the cake_lpr detail rests on the BRIEF R-V8 statement. |
| `subercaseaux2024hexagonlean` | yes | L137 Lean verification that the encoding is faithful, joined to the cake_lpr check; L137 "The hexagon verification and ours both reduce the mathematical statement, in Lean, to the unsatisfiability of a formula defined in Lean" | partial | DataCite abstract supports the Lean formalization of the encoding. The v9 rewording ("The hexagon verification and ours") now attributes the Lean reduction to the combined hexagon verification, not to the TACAS paper alone; the review m1 antecedent defect is resolved. |
| `heule2011cube` | yes | L137 cube-and-conquer | unverified (source not on disk) | Standard attribution. |

**Totals.** supports 0, partial 6, unverified 10, does-not-support 0.

## Changes since the v8 audit

- `\lratcheck`/`Erdos85LratRuntime.lean` clause removed (v8 m2): no uncited checker reference remains.
- Brace protection applied to `{B}oolean`, `{S}chur`, and the whole `bloom-erdos85` title (v8 N4): rendered bibliography shows "Boolean", "Schur", "Erdős Problem #85".
- `heule2024hexagon` carries pages 61--80 and no volume (Crossref has none); acceptable.
