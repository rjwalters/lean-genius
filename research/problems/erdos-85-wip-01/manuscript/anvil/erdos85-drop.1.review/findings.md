# Findings — erdos85-drop.1 (cross-section observations)

## Scope discipline (the BRIEF's hard rules) — mostly held

Checked every occurrence of *theorem*, *proof*, *proved*, *decided*, *conjecture*, *first*, *settle*, *Erdős 85* against the BRIEF's "Hard scope rules":

- Result A is called "computational evidence", "a computational result, not an unconditional Lean theorem", "verdict-only evidence" — never a theorem or "decided". Held.
- Nothing is claimed about Erdős Problem 85 itself; §8 says so explicitly ("we make no claim about the problem itself"). Held.
- No solver verdict or archived certificate is promoted to a kernel-checked statement; the evidence-levels table refuses each promotion by name. Held.
- A-REG: the abstract and §8 call it a "live hypothesis"; §0 L162 slips to "an axiom/conjecture". Not attributed to the authors, so recorded as `major`, not critical — but it must be fixed before audit.
- Authorship and contributions follow the operator ruling (two AI authors; operator and room infrastructure acknowledged, not authors). Held.
- Boza / Afzaly–McKay citation rules: Boza is engaged for the 35/36 no-drop and the `r(109)`, `r(155)` deductions but the open `r(42)` entry is never mentioned and neither work is `\cite`d; Afzaly–McKay's records are correctly described as lower-bound examples only. Partially held.
- The "first decided strict drop" phrase is absent entirely — permissible under the rule, but it is the paper's strongest honest claim and its absence is why D3 scores 2/5.

## Number traceability — split result

- **Traceable and correct** against `refs/CENSUS.md`, `h1-census-table.tsv`, `cube-tree-check.json`, `axioms.out`: 1,161 / 1,160 / 1; 36 leaves, 35 splits, depth 8, 9.7 + 6.2 core-hours, <5 h wall on 24 cores, 29 leaves < 15 min, hardest leaf ≈ 52 min; 4/12/24 h caps; 1,288 = 1,158 + 96 + 34; 1,191 / 96 / 1 / 97; 34 of 34 with Kissat 0.3–1.7 h; 1,413 run directories; six `native_decide` axioms (three per witness); H7 28 roots after 15 exclusions; H3/H5 2/129 rows; Kissat 4.0.4, CaDiCaL 3.0.1; Lean 4.31.0; base-CNF sha256 `860d8af2…`.
- **Internally inconsistent**: 1,159 (L132) vs 1,160 (L35, L83, L313, L319, CENSUS). Critical flag.
- **Traceable only to `refs/DRAFT.md`** (the adopted prior draft) and citing receipts outside `refs/`: every figure in §Cost to verify and its cube-route projection, "1,322 of 1,412" (L122), 13,351 (L291), 12,019 (L82, L126, L315). Major finding; `paper-audit` will need the receipts.

## Rendering — the paper as printed is not the paper as written

The `\path` override garbles every escaped identifier and statement in the PDF (abstract included); the evidence-levels table overflows its page with the folio inside a cell; the bibliography is empty; section numbers are doubled. The mechanical render gate passed (`_gate.json`: 14 pages, 0 overfull boxes, 0 placeholders) — none of these defects is in its detector set, so the pass should not be read as a clean render.

## Structure — a results note wrapped in a process memoir

Ordering as rendered: Main results (1) → Mathematical status (2) → seven process essays (3–9) → Silence is not success (10) → Methods (11) → Results and evidence map (12) → Interpretation (13) → empty References. The BRIEF allows the negative map and campaign-process sections to be shortened or moved to appendices; the reviewer recommends: Introduction → Preliminaries and strata → Result A (evidence levels, trust boundary, cost to verify, cube route) → Theorem B (reduction chain, negative map condensed) → Related work → Interpretation (§8, intact) → Data availability → Appendices (campaign process; artifact index). Sections that the BRIEF says must survive in substance — the evidence-level table, the trust-boundary discussion, the cost-to-verify section, and §8 — are all present and should be kept.

## Underclaiming / buried-lede (cold-reader check, D3/D9)

Central idea extractable from abstract + first section? Only partially: "computational evidence for f(49) = 7 < 8 = f(48), and a Lean-checked reduction of ¬Erdős 85 to A-REG" can be assembled, but the problem itself is not stated, the significance is not stated, and the rendered abstract's headline line is `f(48)\=\8`. The BRIEF's strongest honest claim (every input to the formal finite-drop theorem is Lean-checked or receipt-reproducible; the single unproved hypothesis rests on a complete two-solver census with an empty open list; the census scale and the cube-partition closure are the surprising parts) is stated only in fragments across §1.2 and §8. Recorded as `major` in comments.md. Rigor and honesty elsewhere do not compensate: as written the paper reads as a status ledger rather than a result.

## Rubric version transition

Not applicable — this is the first review iteration of the thread; no prior review sibling exists (`prior_rubric_id` omitted from `_summary.md`).

## Conditional tiers (all inactive this pass)

- Venue overlay: `erdos85-drop/.anvil.json` absent → no `_review.venue.json`.
- External-artifact verification (`artifact_verify`): not declared → not run.
- Corpus provenance tier / subject voice tier: no `corpus:` or `subjects:` declarations → inactive.
- Pending markers: none. Evidence drift: NO-SNAPSHOT (treated as clean).
