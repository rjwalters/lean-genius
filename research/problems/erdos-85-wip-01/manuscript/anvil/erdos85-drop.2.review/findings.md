# Findings — erdos85-drop.2 (cross-section observations)

## v1 critical flags — both resolved in the rendered PDF

- **`rendered_formal_statements_garbled`** — cleared. `pdftotext` of `erdos85-drop.2/main.pdf` (16 pages) contains 0 `\_`, 0 `\=`/`\→`/`\¬` and 0 `??`. The abstract renders `f(48) = 8 and f(49) = 7`, the hypothesis renders `hno49 : ¬ C4FreeMinDegreeWitness 49 7`, Theorem B renders `A-REG ⇒ ¬ Erdos85Question`, and every Lean identifier in Tables 1–4 renders with real underscores. The `\renewcommand{\texttt}[1]{\path{#1}}` override is gone; identifiers go through `\DeclareUrlCommand\lean`.
- **`numerical_inconsistency` (1,159 vs 1,160)** — cleared. Every occurrence now reads 1,160 whole-instance rows + 1 cube-partitioned row = 1,161 residual roots (abstract, §1, §4.2, Table 4, §4.6, §6, Artifacts). Table 3's outcomes sum to 24 + 876 + 242 + 16 + 2 = 1,160 and its row counts reconcile pass by pass (1,137 = 876 + 256 + 1 + 4; 261 = 242 + 19; 17 = 16 + 1). The corrected timing figures (2,704 Kissat / 2,996 CaDiCaL core-hours; 1.9 h median; 121 rows > 4 h; 6 rows > 12 h; 14.9 TB) match `refs/CENSUS_TIMING_20260928.md` line for line.

## Scope discipline (the BRIEF's hard rules) — held

Checked every occurrence of *theorem*, *proof*, *proved*, *decided*, *conjecture*, *settle*, *first*, *Erdős 85* in `main.tex`:

- Result A is called "computational evidence", "a computational result, not an unconditional Lean theorem", "verdict-level evidence, not a theorem" and is never a theorem, proof or decided value. The one use of "decided" ("the first strict drop of $f$ decided on the problem's stated domain") is hedged with "To our knowledge, and conditional on that evidence level", as the BRIEF's own wording permits; recorded as `minor` because it is the reserved verb (see comments.md).
- Nothing is claimed about Erdős Problem 85 itself; the "compatible with either answer" sentence sits adjacent to the significance claim in the abstract, §1 and §6.
- A-REG is "an unproved hypothesis with a stated rival, not a conjecture we endorse" (§1); "conjecture" occurs nowhere else. The v1 "axiom/conjecture" slip is gone.
- No solver verdict or archived certificate is promoted: Table 4's "Limit" column refuses each promotion by name, and §4.3 says "No row is promoted from a solver verdict or an archived proof object to a kernel-checked theorem."
- Authorship and the Contributions paragraph are unchanged in substance (two AI authors; operator and room infrastructure acknowledged, not authors).
- Boza is cited for the table and the open $r(42)$ entry; Afzaly–McKay only for lower-bound examples with their status labelled; the $F$/$r$ convention is stated at every quoted value.

## The r(s) ↔ F(N) conversion — agrees with the 2026-09-28 correction

§1 states: $r(s)\le N$ iff every $C_4$-free graph on $N$ vertices has a vertex of degree at most $N-1-s$, i.e. iff $f(N)\le N-s$; hence $r(s)=\min\{N: f(N)\le N-s\}$; and a plateau $r(s)=r(s+1)=N$ gives $f(N)\le N-s-1<N-s\le f(N-1)$, a strict drop at $N-1\to N$. This is exactly the corrected rule appended to `refs/FIRST_DROP_LITERATURE_CHECK.md` (derivation checked independently: $r(s+1)=N$ gives the upper bound at $N$; $r(s)=N>N-1$ gives $f(N-1)\ge N-s$). Applied to $r(41)=r(42)=49$ it yields $f(49)\le 7<8\le f(48)$, as §1 says. The retracted "orders 35 and 36" gloss is absent from v2 (grep: 0 hits), and the significance paragraph makes only the statement the corrected literature check supports ("no consecutive equality that yields an in-domain drop, though some of its entries remain ranges").

## Number traceability — complete

Every number in the body was checked against `refs/`:

- `CENSUS.md` / `CENSUS_TIMING_20260928.md` / `cube-tree-check.json`: 1,416; 96; 1,161; 1,160; 1; 2 / 129 / 28; 1,257; 1,413 run directories; Table 3 in full; \$235; six reclaims; 42,160 / 613,228; `860d8af2…`; 71 / 35 (31 + 4) / 36 / 8; 9.7 + 6.2; 4 h 50 min on 24 cores; 9 leaves < 10 s; 29 < 15 min; 0.87 / 0.96 h; 27 of 32 in 3 s; 1,288 = 1,158 + 96 + 34; 34 of 34, Kissat 0.3–1.7 h; 1,191 / 96 / 1 / 97; 2,704 / 2,996; 1.9 h; 121; 6; 14.9 TB; 6,700; \$70–100; 360; \$70; 4 TB; \$16; \$2,000–2,500. All match.
- `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md` / `h1_replay_fleet_costs_20260910.json`: 12,019; 13,351; 4,831; 25 %; 10 %; 8 h; 6,651; 17.32 d; \$1,276; 6.06 TB; \$0.03/GB; \$182; 48 GiB / 128 GiB; 509 MB / 984 s. All match. "two to four weeks" is a loose gloss of the JSON's 7.9–31.5 planned days (minor).
- `H1_V3_SOLVER_TIMING_20260916.md`: 574; 4,011 s; 4,539 s; 7,102 s; 22 at 14,400 s; the 10.2 h interval as a pipeline interval. All match.
- `CERT_BANK_STATS_20260926.md`: 5.5 GB per Kissat-hour (receipt says 5–6; the worksheet fixes 5.5). "65 to 130 GB" vs the worksheet's printed 60–130 (arithmetic 66–132; nit).
- `AXIOM_AUDIT_COLD_20260927.md` / `axioms.out`: Table 1 in full; six `native_decide` axioms, three per witness; Theorem B standard-axiom-only. All match.
- `H7_CLOSURE_20260915.md`: 43 classes; 15 excluded; 28 roots; enumerator-code-audit caveat. All match.
- `DRAFT.md` (the adopted prior draft, admitted by the BRIEF as a source for numbers that appeared in it): orders 15 and 16; 168 edges (now restricted to the 48-vertex witness); 392 + 14 = 406, $7\times 8$; evidence-vector lengths 19 / 15 / 7 / 2; $r(109)$, $r(155)$; 52 / 47 / 57 groups; 20 authorized attempts; the order-64 partitions. All present in DRAFT.md.
- Cut in v2 as unbacked at revise time: "\$2,600", "12,102 / 1.2 GB / 4.0 GB / 26.5 GB / 22.6 TB", "1,322 of 1,412". The receipts for the latter two have since been added to `refs/` (`CERT_BANK_STATS_20260926.md`, `CENSUS_TIMING_20260928.md`), so the next revision may reinstate the bank statistics and the 1,322 / 1,412 input-identity count if they help the argument.

No new numbers were introduced. The one traceability defect is the paper's own sentence claiming that every number traces to a receipt *named in Section 6* (major; comments.md).

## Rendering and build

Clean `xelatex` + `bibtex` + `xelatex` ×3 (`compile-log.txt`): 0 errors, 0 undefined citations or references, 0 overfull boxes, 32 underfull lines (6 at badness 10000, all on long Lean identifiers). 16 pages: 11 body + Appendix A (1.5 pp) + Appendix B (1.5 pp) + References (1.5 pp). Render gate passed (`_gate.json`). Tables 1–4 fit `\textwidth` with correct rule order and captions; Table 3's Cap column wraps a lone "h". The bibliography renders 11 entries in plainnat author–year form.

## Structure — the paper is now a results paper

Introduction (problem, $f$, conversion, both results, significance, non-claims, roadmap) → Related work → Definitions and interface (Tables 1–2) → Result A (witnesses; strata closure with Table 3; evidence levels, Table 4; trust; cost; cube projection) → Theorem B (statement; chain; residue; evidence) → Interpretation → Contributions and availability → Appendix A (negative map) → Appendix B (collaboration record). This is the order the v1 review recommended and the BRIEF's four must-survive sections are all present in substance. The remaining structural cost is restatement (D9) rather than misplacement.

## Underclaiming / buried-lede (cold-reader check, D3/D9) — passes

A cold reader can state from the abstract alone: "computational (two-solver, verdict-only) evidence that $f(49)=7<8=f(48)$, to the authors' knowledge the first strict drop decided at that evidence level, selecting $r(42)=49$; and a standard-axiom Lean proof that the single proposition A-REG implies a negative answer to Erdős 85." That is the BRIEF's strongest honest claim. The one element of the BRIEF's "surprising part" that stays buried is the scale (about 5,700 solver core-hours across about 1,400 hard instances): it reaches the reader only as two separate numbers in §4.6. No `major` buried-lede finding this pass.

## Evidence drift (advisory)

`anvil.lib.evidence_drift check` reports `EVIDENCE-DRIFT` on `refs/**`: `CENSUS_TIMING_20260928.md` and the correction appended to `FIRST_DROP_LITERATURE_CHECK.md` landed after the v2 snapshot. Both were re-weighed here: the timing extract supports every §4.6 figure the changelog had flagged as receipt-less, and the literature-check correction agrees with §1's conversion and with v2's omission of the 35/36 remark. Drift does not change any score or flag.

## Rubric version transition

Not applicable — the prior review sibling `erdos85-drop.1.review/_meta.json` carries `rubric_id: "anvil-pub-v2"`, identical to this review's rubric. Scores 17/44 → 32/44 are directly comparable.

## Conditional tiers (all inactive this pass)

- Venue overlay: `erdos85-drop/.anvil.json` absent → no `_review.venue.json`.
- External-artifact verification (`artifact_verify`): not declared → not run.
- Corpus provenance tier / subject voice tier: no `corpus:` or `subjects:` declarations → inactive.
- Pending markers: none (`erdos85-drop.2.pending/_review.json` clean). Numeric detector: 604 numbers, 0 claims, 0 findings.
