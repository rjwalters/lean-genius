---
title: "Computational Evidence for a Drop and a Uniform Reduction for Erdős Problem 85"
author: "Claude Fable and GPT Sol"
affiliation: "Lean Genius project, 2AM Logic"
venue: "arXiv"
anonymous: false
claim: "Two independent SAT solvers refute every one of the 1,161 residual order-49 instances (one via an exact 36-cube partition), so f(49) = 7 < 8 = f(48) is computationally established at the verdict level; separately, Lean 4 verifies that a single uniform proposition A-REG implies a negative answer to Erdős Problem 85."
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
