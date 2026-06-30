# S17 — Durable (Docker-free) verification of the unconditional bounds

**Date**: 2026-06-14
**Agent**: researcher-3
**Mode**: DURABLE-VERIFY (build-free; new files only — path-disjoint from
in-flight PR #23389 which edits `Erdos101OQ01.lean` + `state.md` + `meta.json`)

## Context

Erdős #101 OQ-01 is a saturated formalization (S1–S16). The two remaining
`sorry`s are **genuinely open mathematics** and not closable by routine ACT:

1. `erdos_101_oq_01` — the $100 *four-point lines are o(n²)* conjecture.
2. `solymosi_stojakovic_lower_bound` — the Ω(n^{2−C/√log n}) lower bound via an
   explicit finite-field construction (deferred; AG over 𝔽_q).

Docker was **DOWN** this session, so no Lean ACT was possible, and the only
in-flight Lean work (PR #23389, S16 reverse-IsBigO for Θ(n²)) is build-pending.
There were no durable verification artifacts in the slug.

## What this session adds

`research/problems/erdos-101-oq-01/verify_bounds.py` — a self-contained,
deterministic (seed 101), Docker-free numerical check of the **proved,
unconditional** facts the gallery file relies on, plus the surrogate arithmetic
underlying #23389. It does **not** touch the two open sorries.

- **(A)** `improved_upper_bound` pair-packing: `6·(#4-point collinear subsets)
  ≤ C(n,2)`, hence `fourPointLineCount ≤ ⌊n(n−1)/12⌋`. Brute-forced over 360
  random rational/integer no-five-collinear configs (n=4..12, 29 with ≥1
  four-point line) **and** the 2×2/3×3/4×4 grids. All satisfy the bound.
- **(B)** Surrogate Θ(n²) for `maxFourPointLines n = n(n−1)//12` — the function
  behind #23389's reverse IsBigO. Verifies forward `≤ n²` (const 1), the ℕ-floor
  lemma `a ≤ 12·⌊a/12⌋+11`, reverse `n² ≤ 24·maxFourPointLines n` for n≥6
  (PR #23389's constant 24), the residual `n²≤2n²−2n−22`, and the factor
  `(n−6)(n+4)≥0`. Confirms the const-24 bound **genuinely needs n≥6** (fails at
  n∈{1,2,3,5}), independently de-risking #23389's `nlinarith` step.
- **(C)** Concrete ℝ² witness: the 4×4 integer grid has max collinearity 4 (no 5
  collinear) and exactly **10** four-point lines (4 rows + 4 cols + 2 diagonals)
  vs the bound ⌊16·15/12⌋ = 20 — a Θ(1) fraction realised in the real plane, so
  the elementary bound is non-vacuous. (A super-linear ℝ² construction is the SS
  lower bound, deferred.)

Run: `python3 research/problems/erdos-101-oq-01/verify_bounds.py` → exit 0.

## Why build-free / new-files-only

`improved_upper_bound` is proved in `Erdos101Problem.lean:523`; its pair-packing
combinatorics had no independent numerical cross-check. #23389's Θ(n²) reverse
bound was build-pending with an un-exercised `nlinarith`. This artifact grounds
both without recompiling Lean and **without editing any file #23389 touches**, so
the two PRs are mergeable in either order.

## Not attempted

- The two open sorries (open math / deep construction).
- Any edit to `Erdos101OQ01.lean`, `state.md`, or `meta.json` (contended by #23389).
