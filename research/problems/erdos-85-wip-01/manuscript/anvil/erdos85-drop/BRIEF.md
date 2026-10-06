---
title: "A Certificate-Checked Drop and a Uniform Reduction for Erdős Problem 85"
author: "Claude Fable and GPT Sol"
affiliation: "Lean Genius project, 2AM Logic"
venue: "arXiv"
anonymous: false
claim: "Every SAT instance behind the 48-to-49 drop now has an unsatisfiability certificate accepted by a formally verified checker (cake_lpr): all 1,160 whole-instance H1 rows, the 36 cube leaves of the hardest row (composed by a standard-axiom Lean lemma), and the 96 historical certificates; with H3/H5/H7 closed as before, f(49) = 7 < 8 = f(48) is a certificate-checked computational result — still not a theorem, because the checks run outside Lean and the H1 semantic bridge, the H5 premises and the H7 t=0 capstone remain open in Lean. Separately, Lean 4 verifies that a single uniform proposition A-REG implies a negative answer to Erdős Problem 85."
keywords:
  - Erdős problems
  - C4-free graphs
  - minimum degree threshold
  - SAT solving
  - Lean 4
  - cube-and-conquer
documentclass: anvil-paper
web_search: false
---

# Brief: the Erdős 85 twin-result paper

This thread adopts an existing, near-final Markdown manuscript (`refs/DRAFT.md`, banked on
`erdos85/integration` as `research/problems/erdos-85-wip-01/manuscript/DRAFT.md`) into the
anvil paper lifecycle for review and revision. Version 1 is a faithful LaTeX conversion of
that draft; later versions may reorganize and tighten it but must not change any factual claim
without a receipt in `refs/`.

## The two results

1. **Result A (computational).** Let `f(n)` be the least `d` such that every graph on `n`
   vertices with minimum degree at least `d` contains a 4-cycle. Explicit graphs checked in Lean
   (via `native_decide`) give `f(48) ≥ 8` and `f(49) ≥ 7`. The upper side at order 49 splits into
   strata H1, H3, H5, H7; H3/H5/H7 are closed by reviewed arguments plus computation; H1 is
   1,257 SAT instances, 96 with 2026-08 drat-trim-verified certificates and 1,161 refuted by
   Kissat 4.0.4 then CaDiCaL 3.0.1 under declared caps (1,160 whole instances; one by an exact
   36-cube partition after it defeated every whole-instance cap up to 24 h). No SAT model, no
   solver disagreement. This is verdict-only evidence, not a proof; the paper prices the
   certificate route and proposes a cheaper cube-partitioned route.
2. **Theorem B (Lean, standard axioms only).** `BinarySquareRegularExclusion` (A-REG: for every
   k ≥ 3 no C4-free 2^k-regular graph on 4^k vertices) implies `¬ Erdos85Question`. A-REG is a
   live hypothesis, not a conjecture the authors endorse; the plane-order reading is the rival.

## Strongest honest claim

Every input to the formal finite-drop theorem is either Lean-checked or reproducible from banked
solver receipts; the one unproved hypothesis (no C4-free 49-vertex graph of minimum degree 7)
now rests on a complete two-solver census with an empty open list. Readers who know SAT-based
combinatorics will find the census scale (about 1,400 hard instances, 5,700 solver core-hours)
and the cube-partition closure of the hardest instance the surprising parts; readers who know
Erdős 85 will find the one-proposition reduction the generative part.

## Hard scope rules (critical if violated)

- Never call Result A a theorem, proof, or "decided". Never claim anything about Erdős
  Problem 85 itself (one drop is compatible with either answer).
- Never call A-REG a conjecture of the authors; it is a hypothesis with a stated rival.
- Never promote a solver verdict or archived certificate to a kernel-checked statement.
- Every number must trace to `refs/CENSUS.md`, `refs/h1-census-table.json`,
  `refs/AXIOM_AUDIT_COLD_20260927.md` or the literature notes; no new numbers.
- Authorship and contributions follow the operator's ruling (Claude Fable and GPT Sol; the
  human operator and the room infrastructure acknowledged, not authors); contribution
  statements must stay transcript-true.
- Cite Boza for the Ramsey table and the open r(42) entry; cite Afzaly–McKay only for their
  example records; keep the "to our knowledge, first decided strict drop" phrase epistemic and
  conditional on the evidence level (see `refs/FIRST_DROP_LITERATURE_CHECK.md`).
- Conventions: `F(N)` / `f(n)` is the Erdős 85 function; Boza's `r(s) = R(C4, K_{1,s})` is the
  Ramsey function; say which is in use whenever a value is quoted.

## Audience and length

Combinatorialists and formal-methods readers. Target 12 to 18 pages plus appendices; the
negative map and the campaign-process sections may be shortened or moved to appendices if the
reviewer finds them digressive, but the evidence-level table, the trust-boundary discussion,
the cost-to-verify section and §8 must survive intact in substance.

## References supplied

`refs/` holds the prior draft, the census summary and table, the cold axiom audit, the
literature check, the erdosproblems post draft and the pause handoff. `refs.bib` holds the
resolvable citations; do not invent others (web search is off).

## Hard rules added 2026-09-28 after the operator's read-through of v4

These two rules are scope rules of the same standing as the ones above: a violation is a critical flag.

- **R-AUD (audience only).** The audience is combinatorialists and formal-methods readers. No sentence may address the project's operator or team. Remove every statement about what is or is not *authorized*, *commissioned*, *budgeted*, *cancelled by the operator* or *gated for publication*; every goal, ticket or board number; every room-message number or other pointer into the private transcript; and every reference to "operator review" or "the operator's publication gate". What the paper may say instead is the reader-relevant fact (e.g. "no certificates were produced for the residual rows", "the certificate bank is not public"). Appendix B may keep its *technical* lessons (what was checked, what failed, why, and what it cost) written for a reader; the governance narrative (goals, authorizations, who decided what, transcript pointers) goes.
- **R-LINK (public links).** Every artifact, receipt, script, ledger or Lean module the paper names is a hyperlink to its public location in the GitHub repository, through one base-URL macro so the base can be switched from the branch to the release tag at publication: `\newcommand{\repobase}{https://github.com/rjwalters/lean-genius/blob/erdos85/integration}` and `\repofile{<path>}{<label>}` expanding to `\href{\repobase/<path>}{\texttt{<label>}}`. Lean modules live under `proofs/Proofs/`; research files under `research/problems/erdos-85-wip-01/`. Things that are not public (the S3 certificate bank, the artifact volume, the room transcript database) are described in one sentence as not published, never as paths or bucket names. Repo-relative paths without a link are not acceptable in §7, Appendix A or anywhere else.

Canonical public paths of the receipts (all on `erdos85/integration`, under `research/problems/erdos-85-wip-01/`): `CENSUS_TIMING_20260928.md`, `CERT_BANK_STATS_20260926.md`, `STRATA_AND_SMALL_ORDERS_20260928.md`, `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md`, `PAUSE_HANDOFF_20260927.md`, `sat49/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `sat49/verify_boza48_nonisomorphism.py`, `q7_h5_closure_ledger/README.md`, `q7_h5_closure_ledger/REVIEWED_RESULT.md`, `q7_h5_closure_ledger/review2065.json`, `q7_h5_closure_ledger/reviewer/REVIEW2065.json`, `phase_b_h1_census_20260927/…`, `AXIOM_AUDIT_COLD_20260927/axioms.out`, `H7_CLOSURE_20260915.md`, `PHASE_B_*`, `Q7_*`, `manuscript/FIRST_DROP_LITERATURE_CHECK.md`, `phase_b_h1_verdict_cloud_20260921/`, `q9_solver_controls/…`, `cayley-census-q11-q13/…`, and the Appendix A ledger directories. The thread's `refs/` copies are working copies for the critics, not citable locations.


## Brief amendment R-CERT (2026-10-06, after the H1 certificate check)

Between v5 and this amendment the H1 stratum was certificate-checked (receipts in `refs/`:
`H1_CERT_RECEIPTS_README_20261006.md`, `h1_cert_census_summary.json`, `h1_cert_census_receipts.tsv`,
`h1_cert_historical96_receipts.jsonl`, `pilot_h1_81494a_leaf_cake_lpr.jsonl`,
`COMPOSITION_AXIOMS_20261006.txt`, `Erdos85H1CubePilot81494a_excerpt.lean`). Version 6 must be
re-framed around that fact. `refs/MAIN_TEX_20261006_H1_CERT_DIRECT_EDITS.tex` is v5 with first-pass
direct edits that already state most of the new facts (sections "Certifying H1 (October 2026)" and
"Why the whole-instance route sufficed"); use it as source text, but the reviser owns the result
and must re-verify every number against the receipts.

**New framing (operator decision).** Lead with certified computation: every SAT instance behind
the drop has a certificate accepted by a formally verified checker. The title is the frontmatter
title above. The abstract, introduction, Result A section, evidence table, trust section,
interpretation (whose heading still says "the price of certainty") and conclusion must tell that
story consistently — the cost-to-verify / cube-projection material becomes the report of what was
run and what it cost, and the "we chose to stop at belief" framing is retired.

**Facts the paper may state (each traces to the refs above).** 1,160/1,160 census rows CERTIFIED:
CNF regenerated by the pinned `v2cnf` emitter and sha-matched to the census; CaDiCaL 3.0.1 with
binary LRAT proof logging; the proof streamed into `cake_lpr` (Tan, Heule, Myreen, TACAS 2021;
`tan2021cakelpr`), success = CaDiCaL `s UNSATISFIABLE` and cake_lpr `s VERIFIED UNSAT`; proofs
checked and discarded, sha256 and length kept. 5.64 TB of binary LRAT; largest proof 36.2 GB;
3,435 solver CPU-hours; 207 checker CPU-hours; 0 rejections; 0 SAT across 1,196 ledgers.
Determinism: three rows certified twice on different instance types with the same binary gave
byte-identical proofs; a macOS build gives different, equally valid proofs. Pilot root
h1_81494a6ef36d3ec9: 36/36 leaves accepted by cake_lpr (30 also by Lean's compiled `LRAT.check`);
the Lean lemma `cnf_unsat_of_h1Cube81494a` (module `Erdos85H1CubePilot81494a.lean`, generic
`cnf_unsat_of_cubeTree` in `Erdos85CubeTreeComposition.lean`) composes them over the Lean-generated
`oneHighFamilyV2SatCnf`, axioms `propext`, `Quot.sound` only. Historical 96: re-checked from
archived DRAT via drat-trim → LRAT, 50 accepted by compiled `LRAT.check`, 46 by cake_lpr, none
rejected. Memory: Std `LRAT.check` needed about 10× the binary proof size in RAM; cake_lpr streams
with a bounded heap (4 GB for most rows, 16 GB for the longest). Cloud cost about $200.

**Scope rules that still hold (critical if violated).** Result A is still never a theorem, proof
or "decided"; cake_lpr is a CakeML-verified checker *outside* Lean, not a Lean kernel check, and
the paper must say so; "certificate-checked" / "checked by a formally verified checker" are the
permitted phrases. Name the remaining gaps every time the status is summarized: the H1 semantic
bridge (row-to-stratum assembly), the three H5 Boolean-exclusion premises, the uninstantiated H7
t=0 capstone, the `native_decide`/`Lean.ofReduceBool` dependence of the lower-side witnesses and
the H7 certificate modules, and admitting external checks into Lean. The 34 capacity-grid slots
outside the frozen source are verdict-only; do not include them in "every H1 instance".
R-AUD and R-LINK still apply: link the new receipts through `\repofile` — public paths
`research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/` (README.md,
h1_cert_census_receipts.tsv, h1_cert_census_summary.json), `h1_cert_full_20261001/`,
`h1_cert_pilot_20261001/` (incl. `COMPOSITION_AXIOMS_20261006.txt`), and the Lean modules above;
no budget/operator/goal language. Contributions: the October 2026 H1 certificate check, including
the Lean cube-tree composition lemma, was run by Claude Opus (authorship line unchanged).

**Also fix in v6 (open items from the v5 manuscript-of-record README).** (a) Audit nit: the §3.1
`Lean.ofReduceBool` identification is a statement about Lean's implementation, not something
`axioms.out` prints — say so. (b) Audit nit: Appendix B "thirteen input hashes" are the 2026-08
grid campaign's inputs, not the thirteen H7 certificate modules — correct it. (c) The abstract
must again disclose that the lower-side witnesses use `native_decide`.
