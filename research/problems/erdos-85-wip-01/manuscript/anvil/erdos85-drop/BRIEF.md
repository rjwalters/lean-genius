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
