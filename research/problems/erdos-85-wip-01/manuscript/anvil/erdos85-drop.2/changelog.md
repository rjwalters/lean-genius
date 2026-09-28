# Changelog — erdos85-drop.1 → erdos85-drop.2

Revised against every critic sibling at version 1: `erdos85-drop.1.review/` (generic rubric
`anvil-pub-v2`, 17/44, two critical flags), `erdos85-drop.1.numeric/` (tool evidence, 0 findings)
and `erdos85-drop.1.pending/` (tool evidence, 0 findings, no `[PENDING]` markers). No venue overlay,
audit, litsearch, vision or corpus-audit sibling exists at version 1.

Build: `xelatex` + `bibtex` + `xelatex` ×3 in `erdos85-drop.2/` (log in `compile-log.txt`): 0 LaTeX
errors, 0 undefined citations or references, 0 overfull boxes, 16 pages (v1: 14 pages with the
process essays in the body; v2: 11 pages of body + 5 pages of appendices and references).
`pdftotext main.pdf` contains no `\_`, `\=`, `\→`, `\¬` or `??` artefacts.

## Structural changes (summary)

- New Introduction (problem statement, definition of $f$, Boza's $r$ with the conversion rule,
  Result A and Theorem B in plain mathematics, the significance claim with the epistemic qualifier
  and the $r(42)\in\{49,50\}$ connection, the strata and the "exhaustiveness is the consumer's
  interface" statement, a what-we-do-not-claim paragraph, a roadmap).
- New Related Work section drawn only from the 11 `refs.bib` entries and
  `refs/FIRST_DROP_LITERATURE_CHECK.md`; all 11 entries are now cited (`\citep`/`\citet`/
  `\citeyearpar` per the natbib author-year rule).
- New Section 3 "Definitions and the formal interface" with Table 1 (audited Lean statements →
  content → axiom scope, absorbing `refs/axioms.out`) and Table 2 (consumer inputs).
- Result A is one section: witnesses; closure of each stratum (H3/H5, H7, H1 with a census-pass
  table, Table 3, and the cube procedure spelled out); evidence-level table (Table 4); "Where the
  residual trust sits"; cost to verify; cube-partitioned projection. All four survive in substance.
- Theorem B is one section: statement, the reduction chain stated once, the residue
  (defect operator, NONBIP-CONNECTED, socket), evidence for and against A-REG.
- Interpretation (old hand-numbered §8) kept intact in substance, renumbered by LaTeX, with the
  "reconciled on 2026-09-28" meta-paragraph replaced by an "Artifacts" paragraph naming the three
  artifacts by repository path.
- Contributions paragraph kept as written (only "§8" re-pointed to `\ref{sec:interpretation}`);
  new "Data and code availability" paragraph.
- Appendix A "The negative map for A-REG" (condensed negative map, 63-to-64 status, plane-order
  censuses; ledger/commit/room pointers allowed here as transcript pointers).
- Appendix B "The collaboration record" (old hand-numbered §§1–7, "Silence is not success",
  the h305 case study and the Methods bullets, condensed to about 1.5 pages).
- Hand-typed section numbers removed; all cross-references are `\label`/`\ref`.
- `figures/` carried over (empty in v1, empty in v2; no `figures/src/`).

## Critical flags

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.1.review (generic, critical `rendered_formal_statements_garbled`) | `\renewcommand{\texttt}[1]{\path{#1}}` printed pandoc's escape backslashes in every Lean statement, abstract included | Override removed. Mathematics is set in math mode ($f(48)=8$, $f(49)=7$, $\mathrm{A\text{-}REG}\Rightarrow\neg\,\textsf{Erdos85Question}$, $r(s)=R(C_4,K_{1,s})$, $A^2=(q-1)I+J-D$, the defect-component identities). Lean identifiers are set through a dedicated `\DeclareUrlCommand\lean{\urlstyle{tt}}` command written with raw underscores (url-style breaking at `_` and `.`; `\texttt{}` where an identifier contains spaces or sits in a caption), plus `\usepackage[htt]{hyphenat}`; `\sloppy` replaced by `\tolerance=800` + `\emergencystretch=3em`. `pdftotext` grep for `\_`/`\=`/`\→`/`\¬`: 0 hits. |
| erdos85-drop.1.review (generic, critical `numerical_inconsistency`) | "1,159 UNSAT verdicts needed 2,695 Kissat core-hours … 120 rows above 4 hours … about 15 TB" (cube-route subsection) vs 1,160 everywhere else and in `refs/CENSUS.md` | Corrected everywhere to the figures recomputed from the receipts on 2026-09-28 and supplied by the dispatcher: 1,160 whole-instance UNSAT rows (plus 1 by the cube partition = 1,161); 2,704 Kissat core-hours and 2,996 CaDiCaL core-hours; median 1.9 h of Kissat per row; 121 rows above 4 h and 6 above 12 h; about 14.9 TB at 5.5 GB per Kissat-hour. The v1 figures were the 2026-09-26 partial join. The text now says "1,160 whole-instance UNSAT rows" so the count matches `CENSUS.md` on its face. Traceability note: the per-row timing join is not itself a file in `refs/` (`h1-census-table.tsv` carries id/sector/status/attempts only); the numbers are the dispatcher's recomputation from the Stripe receipts and should be added to `refs/` as a timing extract before audit. |

## Major

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.1.review (generic, major) | Abstract + missing Introduction: buried lede, problem never stated, no significance, no `r(42)`, no "to our knowledge" | Abstract rewritten to state the problem, both results in plain mathematics, the evidence level, the significance with the epistemic qualifier and the `r(42)=49` selection, and "one drop is compatible with either answer". New Section 1 with the five requested items (problem and $f$; both results; significance with qualifier and `\citep{boza2024ramsey}`; strata; roadmap). The "compatible with either answer" sentence sits adjacent to the significance claim. |
| erdos85-drop.1.review (generic, major) | Zero `\cite`, empty rendered References | All 11 `refs.bib` entries cited at natural first mention (Bloom ×2, Boza ×4, Zhang–Chen–Cheng ×3, Afzaly–McKay ×2, Kissat, CaDiCaL, cube-and-conquer ×2, Pythagorean triples, DRAT-trim, LRAT, Lean 4 ×2, mathlib ×2). The two `\href` links replaced by `\citet`. BibTeX runs with no warnings; References renders 11 entries. `refs.bib` hygiene: `year = {n.d.}` added to the two undated web entries so natbib does not print an empty year; `{Erd\H{o}s}` brace-protected in the Bloom title so plainnat's case change does not lowercase the accent command. |
| erdos85-drop.1.review (generic, major) | No Related Work section | New Section 2 with four paragraphs: the problem and its Ramsey form (Bloom, Zhang–Chen–Cheng, Boza with the $F$/$r$ convention); extremal records at order 49 (Afzaly–McKay as lower-bound examples only, 174 edges, minimum degree 6, per the literature check); SAT solving with and without certificates (Kissat, CaDiCaL, DRAT-trim, LRAT, cube-and-conquer, Pythagorean triples as the verdict-vs-certificate model); the trust root (Lean 4, mathlib). Nothing beyond the 11 entries and the literature check is cited. |
| erdos85-drop.1.review (generic, major) | "A-REG itself remains an axiom/conjecture" (old §0 L162) | Replaced by "remains an unproved hypothesis"; the phrase "unproved hypothesis with a stated rival" is used consistently in the abstract, Section 1, Section 5 and Section 6. The only remaining occurrence of "conjecture" is the BRIEF's own formulation "not a conjecture we endorse". |
| erdos85-drop.1.review (generic, major) | Cost-to-verify numbers untraceable to `refs/` | The two `sat49/*.md` receipts and `h1_replay_fleet_costs_20260910.json` are now in `refs/`, and every retained cost figure traces to them: 12,019 / 4,831 / 25% / 10% / 8 h / 6,651 / 17.32 d / \$1,276 / 6.06 TB / \$0.03/GB / \$182 / 13,351 / 1,288 (budget plan); 574 / 4,011 s / 4,539 s / 7,102 s / 22 / 14,400 s / 10.2 h pipeline interval (timing readback); 509 MB / 984 s (fleet-cost JSON); 48 GiB gate / 128 GiB lane / two-to-four weeks (budget plan and JSON wall-day rows). **Cut** (no receipt in `refs/`; they existed only in `refs/DRAFT.md`): the "\$2,600 proxy" dollar figure (the sentence now explains why the proxy is not a forecast without quoting it), the archived-bank statistics "12,102 verified rows, median 1.2 GB, p90 4.0 GB, largest 26.5 GB, 22.6 TB", and "1,322 of the 1,412 input preparations" (replaced by the qualitative statement that the pipeline compares each emitted CNF against the 2026-08 producer's hash). **Retained as labelled projections** per the BRIEF's "cube-partitioned projection must survive in substance": 6,700 core-hours, \$70–100, 360 host-hours, \$70, 4 TB, \$16/month, \$2,000–2,500 — the paragraph states they are projections from the bank's rate and one cube tree, not receipts; they trace only to `refs/DRAFT.md`, and a projection worksheet should be added to `refs/` before audit. |
| erdos85-drop.1.review (generic, major) | Hand-numbered section titles inside auto-numbered sections; dangling "§8" | All hand numbers removed; sections ordered deliberately (Intro → Related work → Definitions/interface → Result A → Theorem B → Interpretation → Contributions/availability → Appendices A, B); every cross-reference is `\ref` (`sec:strata`, `sec:cost`, `sec:cube`, `sec:theoremB`, `sec:interpretation`, `sec:artifacts`, `app:negative`, `app:collab`, table labels). |
| erdos85-drop.1.review (generic, major) | Campaign-process essays in the body; `room msg`/`outline v2.6x`/commit-hash citations in the body | Moved and condensed into Appendix B "The collaboration record" (verification asymmetry, the h305 case study, adversarial diversity, exchange rate, persistence, scope words, the human role, why Erdős problems, silence is not success, Methods bullets). The main body contains no room-message numbers, outline versions or commit hashes; they remain only in Appendices A and B, which state that they are transcript pointers. |
| erdos85-drop.1.review (generic, major) | §8 "reconciled on 2026-09-28" meta-paragraph | Deleted. The three artifacts it named are kept as a short "Artifacts" paragraph (`\label{sec:artifacts}`) inside Section 6 with their repository paths, plus a separate "Data and code availability" paragraph in Section 7 listing the branch, receipt directories, tooling, artifact volume with checksum manifest, private bucket and the non-isomorphism script. |
| erdos85-drop.1.review (generic, major) | Evidence-levels table: rules in the wrong order, no caption/number/label, 54.8 pt overflow, folio inside a cell; same caption fix for the four-input table | Both rebuilt as `table` + `tabularx` (`\toprule`/`\midrule`/`\bottomrule` in order, `\caption`, `\label`, widths that fit `\textwidth`); the 1,288-slot accounting shortened in the cell and carried in prose (Section 4.2). `longtable` is not loaded. Log: 0 overfull boxes, no "Float too large". Float fractions raised so the evidence table sits with text rather than on a float page. Two further captioned tables added (audited statements; census passes). |
| erdos85-drop.1.review (generic, major) | "168 edges … corroborate both graphs" | Restricted: "the 48-vertex witness has 168 edges and all pair codegrees at most 1, and the 49-vertex witness passes the same codegree check". No edge count is stated for the 49-vertex witness (none is in `refs/`). |
| erdos85-drop.1.review (generic, major) | Strata never defined; exhaustiveness not stated | Section 3.2 defines the strata as indexed by the high-vertex count $h\in\{1,3,5,7\}$ ("one-high" through "seven-high" in the source), says the normalization and the exact meaning of "high" are fixed by the Lean definitions, and states that exhaustiveness is the Lean consumer's own interface (the consumer derives `hno49` from exactly the four inputs of Table 2). Section 4.2 summarizes the H3/H5 closure (two cover formulas, $7\times 8$ grids, 392 + 14 = 406 jobs proved in Lean, 2 and 129 census rows) and the H7 closure (43 classes, 15 excluded, 28 roots covered; enumerator-code audit caveat; uninstantiated capstone) in the paper rather than by ledger pointer alone. Not applied beyond the receipts: the paper does not restate the normalization itself, because no `refs/` document states it and inventing one would be a new claim. |

## Minor

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.1.review (generic, minor) | Abstract opens with `f(n) = minDegreeForC4 n` | Abstract and Section 1 define $f(n)$ in mathematics first; the Lean name is given once in Section 1 and again in Section 3.1. |
| erdos85-drop.1.review (generic, minor) | AI-tell adjective class: *honest* ×11, *candid* ×3, *genuinely* ×1 | All removed or replaced by the concrete referent ("the remaining residue", "the corrected 88-owner table" → "the actual h305 shore modes", "regular hypotheses", "the statement we can make", "an unproved infinite frontier"). The old "5. Honest scoping" title is now "Scope words" in Appendix B. Strict grep for `honest|candid|genuinely|load-bearing`: 0 hits. |
| erdos85-drop.1.review (generic, minor) | §Theorem B and §0 duplicate the reduction chain | Collapsed to one statement: Section 5.1 (chain) and 5.2 (residue). |
| erdos85-drop.1.review (generic, minor) | §Results and evidence map restates the chain a third time; suggested a table of Lean names → statements → axiom status | Section removed; its content became Table 1 (audited statements with axiom scope, from `refs/axioms.out`) and the one-paragraph chain in Section 5.1. |
| erdos85-drop.1.review (generic, minor) | `\href` to DOI/arXiv in running text | Replaced by `\citet{zhang2017polarity}` and `\citet{boza2024ramsey}` (now in Appendix A). |
| erdos85-drop.1.review (generic, minor) | Underfull `\hbox` ×9 from `\path`+`\sloppy` | `\sloppy` removed; 0 overfull boxes. 32 underfull warnings remain (badness ≥ 1000; six at 10000), all on lines carrying long Lean identifiers with url-style breakpoints only at underscores; visually checked on the rendered pages and judged acceptable. Not silenced with `\hbadness`. |
| erdos85-drop.1.review (generic, minor) | Conventions: the abstract's Boza 35/36 remark silently converts $r(35)=42$, $r(36)=43$ | **Cut rather than converted.** The conversion is now stated explicitly in Section 1 ($r(s)=\min\{N: f(N)\le N-s\}$). Under it, $r(35)=42$ and $r(36)=43$ are statements about $f$ at orders 41–43, not at orders 35 and 36, so the literature check's gloss "$F(35)=F(36)=7$" does not follow from the entries it quotes; the "no-drop behaviour at orders 35 and 36" remark therefore cannot be stated together with the conversion without either repeating an unsupported gloss or contradicting it. It is removed; the A-REG evidence paragraph keeps the Lean-checked orders 15/16 statement and the failed generic terminals. Recommend the authors re-derive the $q=6$ plane-order values from Boza's $r(28)$–$r(30)$ entries before reinstating any 35/36 remark. |

## Nit

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.1.review (generic, nit) | Display statements set as `\texttt` paragraphs | Set in `\[ … \]` or in `amsthm` environments (`Result A`, `Hypothesis A-REG`, `Theorem B`, `NONBIP-CONNECTED`). |
| erdos85-drop.1.review (generic, nit) | `\rule` separators | Removed. |
| erdos85-drop.1.review (generic, nit) | Working-manuscript status comment | Removed from the source. |
| erdos85-drop.1.review (generic, nit) | `\date{2026-09-28}` | Changed to `\date{28 September 2026}` (kept a date for version identification of a working manuscript; declined to remove it entirely). |
| erdos85-drop.1.review (generic, nit) | Procedural notes (numeric detector, pending gate, drift, render gate) | Noted. Evidence-drift baseline re-recorded for `erdos85-drop.2/` by `anvil.lib.evidence_drift record` (see `_progress.json`). |

## Other siblings

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.1.numeric (tool evidence) | 420 numbers, 0 arithmetic claims, 0 findings | Nothing to apply. The new census-pass table's outcomes sum to 1,160 (24 + 876 + 242 + 16 + 2) and the index decomposition sums to 1,416 (96 + 1,161 + 2 + 129 + 28), so the next numeric pass has checkable arithmetic. |
| erdos85-drop.1.pending (tool evidence) | No `[PENDING]` markers | Nothing to carry forward; v2 contains no markers. |

## Dispatcher instructions applied beyond the review

- Corrected census/timing figures (critical flag 2) used everywhere they appear (Sections 4.6 and 6 and the abstract count).
- BRIEF hard scope rules re-checked on v2: Result A is never called a theorem/proof/decided; nothing is claimed about Erdős 85 itself; A-REG is "an unproved hypothesis"/"live hypothesis" with the plane-order reading as rival; no verdict or certificate is promoted; authorship and the Contributions paragraph unchanged in substance.
- Not applied / left for the authors: (i) the two `refs/`-gap items above (timing extract for the 1,160-row join; projection worksheet for Section 4.6); (ii) reinstating the Boza 35/36 remark after re-derivation.
