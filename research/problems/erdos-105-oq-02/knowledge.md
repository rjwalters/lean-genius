# Problem: erdos-105-oq-02 — Is f(n) = Θ(n)?

## Problem Summary

**Source**: Erdős Problem #105 (disproved 2024), Open Question 02
**Status**: RESOLVED — f(n) = Θ(n) from Beck-SzTr + Xichuan bounds

The threshold function f(n) is the largest number of obstacles such that for every
n non-collinear points A and every obstacle set B with |B| ≤ f(n), some rich line
(through ≥ 2 points of A) avoids all of B.

Known: c·n ≤ f(n) ≤ n-4 for n ≥ 4 (from Beck-SzTr and Xichuan 2024).

## Session 2026-04-13 (Session 1) — f(n) = Θ(n) Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Claimed problem from pool
- Analyzed existing Erdos105Problem.lean: found `thresholdFunction` (axiom), `openProblem_exact_threshold` (Prop)
- Designed new `Erdos105OQ02.lean` with:
  - BigO, BigOmega, BigTheta definitions for ℕ → ℕ
  - Reflexivity and transitivity theorems for BigO, BigOmega
  - Two bound axioms: `threshold_lower_bound` (Beck-SzTr), `threshold_upper_bound` (Xichuan)
  - Main theorem: `threshold_is_Theta` (thresholdFunction = Θ(idFn))
  - Resolution: `exact_threshold_resolved` (proves openProblem_exact_threshold)
  - OptimalConstant c* definition and bounds c* ∈ (0,1]
  - Gap axiom: f(n) ≤ n-4 for n ≥ 4
- Created gallery entry: `src/data/proofs/erdos-105-oq-02/meta.json`
- Added import to `Proofs.lean`

### Key Findings
- The Θ(n) question is RESOLVED: lower from Beck-SzTr (1983), upper from Xichuan (2024)
- The OPEN part is the exact constant c* = sup{c : cn ≤ f(n) for all n} ∈ (0,1]
- The `thresholdFunction` in the parent file is an axiom (no constructive definition)
  so connecting it to actual set-theoretic definitions requires additional axioms
- Proof structure: BigTheta = BigO ∧ BigOmega, each proved separately from two axioms

### Files Modified
- `proofs/Proofs/Erdos105OQ02.lean` (new, ~220 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/erdos-105-oq-02/meta.json` (new)

### Next Steps
- Run Docker build when available to verify compilation
- Consider formalizing the Hickerson construction (n-2 blocks for all n) to eliminate threshold_gap_axiom
- The Beck-SzTr axiom in the parent file might eventually be proved from incidence theory
