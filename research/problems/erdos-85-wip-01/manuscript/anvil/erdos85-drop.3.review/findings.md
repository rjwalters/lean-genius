# Findings — erdos85-drop.3 (cross-section observations)

## Scope discipline (the BRIEF's hard rules) — held

Checked every occurrence of *theorem*, *proof*, *proved*, *decided*, *conjecture*, *settled*, *first*, *Erdős 85* / *Problem 85* in `main.tex`:

- Result A is "computational evidence", "a computational result, not an unconditional Lean theorem", "verdict-level evidence, not a theorem", "evidence, not a theorem"; the Result A box says "The combined evidence supports". The word *decided* no longer applies to Result A anywhere (its five occurrences are "Boza's decided table", "undecided candidate", "never called … a decided value", "how the decided entries of the $r$ table were obtained", "63-to-64 is not a decided drop"). "Settled" is used for the drop "at the level of computational evidence" and for the residual roots, as the BRIEF's own wording permits.
- Nothing is claimed about Erdős Problem 85 itself; the "compatible with either answer" sentence sits beside the significance claim in the abstract, §1 and §6.
- A-REG is "an unproved hypothesis with a stated rival, not a conjecture we endorse" (§1) and "an unproved hypothesis, not a forecast" (abstract); *conjecture* occurs nowhere else.
- No solver verdict or archived certificate is promoted: Table 4's Limit column refuses each promotion by name; §4.3 says "No row is promoted from a solver verdict or an archived proof object to a kernel-checked theorem."
- Authorship and the Contributions paragraph are unchanged in substance (two AI authors; operator and room infrastructure acknowledged, not authors).
- Boza is cited for the table and the open $r(42)$ entry; Afzaly–McKay only for lower-bound examples with their status labelled; the $F$/$r$ convention is stated at every quoted value; the priority phrase is "To our knowledge … settled, at the level of computational evidence".
- The default AI-tell check (honest/candid/frank/uncomfortable/painful/humbling/load-bearing) finds no instance; the room vocabulary (cold-green, jaw, socket, monoliths, pincers) is gone.

## The new §3.2 strata definitions and Table 2 — verified against `STRATA_AND_SMALL_ORDERS_20260928.md`

- High vertex = degree exactly 8 (`orderFortyNineHighVertices G`): matches. The paper's derivation that every degree is 7 or 8 and that a degree-8 vertex has only degree-7 neighbours (non-returning length-two walks from $v$ have distinct endpoints, so $\sum_{u\sim v}(\deg u-1)\le 48$) was re-derived independently and is correct: $6d\le 48$ gives $d\le 8$; for $d=8$ the sum forces all eight neighbours to degree 7.
- $h$ odd from $7\cdot 49+h$ even: correct. $h\le 9$: attributed to "the $C_4$-free edge bound"; the receipt says "an upper bound from the C4-free edge count keeps h ≤ 9" and the Lean theorem `orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine` is named. The standard $\mathrm{ex}(49,C_4)\le 182$ does not give $h\le 9$ (minor; comments.md).
- `OrderFortyNineStratumExcluded h`, `orderFortyNineStratumExcluded_nine` via `false_of_orderFortyNine_nine_high`, and the displayed combining theorem `not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata (h1)(h3)(h5)(h7)`: all match the receipt, which the reviser reports was grep-verified against `proofs/Proofs/` on 2026-09-28.
- Table 2 rows 1/3/5/7/9 (the `…_of_pureFamilies`, `…_of_tripleCells` with cells $t=0,1$ / $t=0,1,2$ / $t=0,\dots,7$ bounded by `orderFortyNine_highIncidence_profile_of_seven_high`, and `…_nine`): all match the receipt's table, including the evidence column (census with the open row-to-stratum assembly; LRAT proofs of `orderFortyNineGeneratedCanonicalSatCnf` at `threeHighRepresentativeMasks`; reviewed cover at `fiveHighRepresentativeMasks`; the 2026-09-15 ledger with the capstone `…_seven_of_emptyCubeEvidenceVectors` (19/15/7/2) uninstantiated; proved in Lean).
- The abstract's "a case split, proved exhaustive in Lean" and §1's "Lean proves that the number $h$ of degree-8 vertices is odd and at most 9 and that $h=9$ is impossible" are supported by the receipt. §5.3's `minDegreeForC4_fifteen` / `_sixteen`, `fifteenRegular` / `sixteenRegular` and the $q=4$ remark match the receipt's small-orders section.

## The §4.2 closure sketches — verified against the inventories, the squeezes and `H7_CLOSURE_20260915.md`

- **H3/H5.** Block form, independence of high vertices, exactly one common neighbour per pair of high vertices (a consequence of the 48-endpoint count for a degree-8 vertex), support $\le 3$ from the matching structure: consistent with `Q7_H5_H7_SQUEEZE` ("High vertices are independent", $A=[0\,B;B^T\,C]$) and `Q7_H1_H3_SQUEEZE` ("each pair of highs has one common low neighbor"). The H3 tables (25,18,3,0) and (24,21,0,1) are the incidence-profile table of `Q7_H1_H3_SQUEEZE` (which calls them profiles, not cells — minor); the H5 tables (14,20,10,0), (13,23,7,1), (12,26,4,2) are the support census of `Q7_H5_H7_SQUEEZE`. Each row was checked: sizes sum to $49-h$, incidences to $8h$, pairs to $\binom{h}{2}$. The two H3 base CNFs (29,500 variables, 1,328,183 clauses) and the H5 root count (58 per cell, 15 direct certificates, 43 remaining, 129 rows) match `PHASE_B_H1_H3_INVENTORY` and `PHASE_B_H5_H7_INVENTORY`; the checked LRAT proofs for both H3 cells and the independent H3 exclusion (review 1685) match `STRATA_AND_SMALL_ORDERS` and `Q7_H1_H3_SQUEEZE`. The 392 + 14 = 406 grid and the two Lean accounting names trace to `DRAFT.md` (admitted by the BRIEF). **Unreconciled**: "the seven whole-cell H3/H5 formulas" vs the two H3 + three H5 representative formulas (major; comments.md). **Missing**: the H5 closure outcome and its receipt (major; comments.md).
- **H7.** The 7/14/21 split is the H7/T0 row of `Q7_H5_H7_SQUEEZE`; the 43 subcubic $C_4$-free classes at $a=6..9$, the singleton-capacity argument ($\max(0,35-4a)$; capacity $7-2d_E$; 12 classes at $a=6$ and 3 at $a=7$; 7/12/7/2 survivors), the Lean pieces (`Erdos85VertexSubsetEdgeCapacity.lean`; $\deg_X v+2n_E(v)\le 7$ in `…ExteriorPairCapacity.lean`; $35\le 4a+|X|$, all standard axioms) and the non-Lean pieces (the enumeration, the representative certificates, the isomorphism transfer) all match the squeeze. The per-family routes (A6 source cover → high assignments → quotient cover; A7 source enumeration with complement completion; A8 singleton normalization; A9 maximum-high normalization with twin6 and crossed14), the F12/F14 exact partitions, $2{,}278{,}608 = 1{,}757{,}882 + 75{,}027 + 445{,}699$, the third-seat reproduction with zero mismatches, and the two caveats (enumerator-code audit for A7 completeness; uninstantiated capstone) all match `H7_CLOSURE_20260915.md`. **Omitted**: the C7 chain that closes `cube_F7_t14` (minor). **Gap**: what excludes cells $t=1,\dots,7$ so that the T0 profile is the whole stratum is neither stated nor receipted (major; comments.md).
- **H1.** The instance description (unique high vertex with a perfect-matching neighbourhood; every other vertex with exactly one neighbour there; a 6-regular $C_4$-free graph on the remaining 40 vertices with eight attachment groups of five) is `Q7_H1_H3_SQUEEZE` verbatim in substance; the five profile counts 283/346/388/198/42, the 24 table values and the `v2cnf emit`/`check` interface are `PHASE_B_H1_H3_INVENTORY`. The census paragraph, Table 3, the cube tree, the capacity-grid decomposition and the auditor counts match `CENSUS.md` and `cube-tree-check.json` as in v2; the three-residual-roots explanation uses the inventory's term "historical object conflicts" (the mechanism is a reading — minor).

## The §7 receipt list — every named file is present

`CENSUS.md`, `h1-gap1288-audit.json`, `cube-tree-check.json` (named as `cube-h1_…/tree-check.json`), `h1-census-table.json` (`refs/` holds the `.tsv` twin; `CENSUS.md` names both), `CENSUS_TIMING_20260928.md`, `CERT_BANK_STATS_20260926.md`, `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md`, `h1_replay_fleet_costs_20260910.json`, `H1_V3_SOLVER_TIMING_20260916.md`, `AXIOM_AUDIT_COLD_20260927.md` + `axioms.out`, `STRATA_AND_SMALL_ORDERS_20260928.md`, the two Phase B inventories, the two Q7 squeezes, `H7_CLOSURE_20260915.md`, `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt` (PASS; 10 archive graphs; unique 7-regular index 9; NetworkX 3.6.1 per the strata note), `FIRST_DROP_LITERATURE_CHECK.md` with its dated correction. The figures each entry claims to carry were spot-checked against the file (timing: 2,704 / 2,996 / 1.9 h / 121 / 6 / 5,716 / 1,322 of 1,412 and the worksheet; bank: 12,102 / 1.2 / 4.0 / 26.5 GB / 22.6 TB / 984 s / 509 MB; replay: 12,019 / 4,831 / 6,651 / 17.32 d / \$1,276 / 6.06 TB / \$182 / 48 GiB / 128 GiB / 7.88–31.48 planned days; v3: 574 / 4,011 / 4,539 / 7,102 / 22 / 10.2 h). All match. Not named in §7 but carrying body numbers: `PAUSE_HANDOFF_20260927.md` / `DRAFT.md` (the `v2cnf` hash `4bd9604c…`; the §5.3 census orders) — minor.

## Number traceability — complete except as noted

Every figure in Sections 1–7 was checked against `refs/`; the only residual exceptions are the two in the preceding paragraph and the "about 1,400 solver inputs" gloss (1,412 preparations for 1,161 rows — minor). No new number was introduced without a receipt; the H3/H5/H7 figures newly added in v3 all trace to the four stratum documents, the H7 ledger or `DRAFT.md`. The two ranges corrected in v2's review now match the receipts ("one to four and a half weeks … 8 to 32 planned days at 32 to 8 shards"; "roughly 60 to 130 GB").

## Rendering and build

Clean `xelatex` + `bibtex` + `xelatex` ×2 (`compile-log.txt`): 0 errors, 0 undefined citations or references, 0 overfull boxes, 23 underfull lines (six at badness 10000, all on three-identifier sentences). 18 pages: about 12.5 body + Appendix A (1.5) + Appendix B (2.5) + References (1). Render gate passed (`_gate.json`). `pdftotext`: 0 `\_`, 0 `??`, 0 `n.d.`, 0 `[?]`; Table 3's Cap cell renders on one line; the bibliography renders 11 entries; in-text "Bloom, 2026" and "Afzaly and McKay (2026)". Table 2's Lean identifiers break mid-name in the rendered cells (D6).

## Structure and the cold-reader check — pass

Introduction (problem, conversion, both results with scale, significance, non-claims, roadmap) → Related work → Definitions and interface (Tables 1–2) → Result A (witnesses; strata with sketches and Table 3; evidence levels, Table 4; trust; cost; cube projection) → Theorem B → Interpretation → Contributions, receipts, availability → Appendices. A cold reader states from the abstract alone: "two-solver verdict-only computational evidence that $f(49)=7<8=f(48)$, to the authors' knowledge the first strict drop of $f$ settled at that evidence level, corresponding to $r(42)=49$; and a standard-axiom Lean proof that A-REG implies a negative answer to Erdős 85." That is the BRIEF's strongest honest claim; the scale is now in §1. No underclaiming or buried-lede finding.

## Prior-review items (v2) — disposition

All six v2 majors were addressed as the changelog states, five substantively and one (related-work method lineage) declined with reason; all eleven minors and four nits were applied. The v3 additions expose three new majors of a narrower kind (H7 $t\ge 1$ premise; the seven-vs-five formula count; the H5 closure outcome), all of which need a receipt from the authors rather than prose from the reviser; the reviser's refusal to invent them is correct.

## Evidence drift

`anvil.lib.evidence_drift check` reports `CLEAN`: `BRIEF.md` and `refs/**` are unchanged since the v3 revise snapshot. No note in verdict.md.

## Rubric version transition

Not applicable — `erdos85-drop.2.review/_meta.json` carries `rubric_id: "anvil-pub-v2"`, identical to this review's rubric. Scores 32/44 → 35/44 are directly comparable.

## Conditional tiers (all inactive this pass)

- Venue overlay: `erdos85-drop/.anvil.json` absent → no `_review.venue.json`.
- External-artifact verification (`artifact_verify`): not declared → not run.
- Corpus provenance tier / subject voice tier: no `corpus:` or `subjects:` declarations → inactive.
- Pending markers: none (`erdos85-drop.3.pending/_review.json` clean). Numeric detector: 764 numbers, 0 claims, 0 findings (`erdos85-drop.3.numeric/_review.json`).
