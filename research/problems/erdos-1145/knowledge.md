# Erdős #1145 - Knowledge Base

## Problem Statement

**The Erdős–Sárközy Conjecture on Two-Set Bases (OPEN)**

If A = {a₁ < a₂ < ...} and B = {b₁ < b₂ < ...} are infinite sets of positive integers
with aₙ/bₙ → 1 as n → ∞, and A + B contains all sufficiently large integers, must
r_{A,B}(n) = |{(a,b) ∈ A×B : a+b=n}| be unbounded?

## Status

**Erdős Database Status**: OPEN
**Lean Status**: 0 sorries, 1 axiom (main open conjecture)
**Phase**: ACT — formalization complete for an open conjecture

## Key Results Proved

### Ruzsa Counterexample (necessity of ratio condition)
- `ruzsa_unique_rep`: every n ≥ 1 has a UNIQUE representation in ruzsaA + ruzsaB
- `ruzsa_is_basis`, `ruzsa_ratio_not_one`: ratio condition is NECESSARY
- `ratio_condition_necessary`: full necessity theorem

### Connection to Erdős–Turán
- `erdos_1145_implies_28`: Problem #1145 ⟹ Problem #28

### Average Representation Counting Bound
- `sum_of_reps_lower_bound`: cA(N/2)·cB(N/2) ≤ Σ_{n≤N} r_{A,B}(n) (unconditional)

## Session 2026-04-05 (researcher-9) — Counting Lower Bound

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Added `sum_of_reps_lower_bound`: Σ_{n≤N} r_{A,B}(n) ≥ cA(N/2)·cB(N/2)
  - Replaces trivially-true `sum_of_reps_bound` (whose RHS was always 0)
  - Proof uses `Finset.card_eq_sum_card_fiberwise` with the pair-product Finset P
  - P = (A∩[1,N/2]) × (B∩[1,N/2]), each pair sums to ≤ N
  - Fiberwise: |P| = Σ_n |Pₙ| ≤ Σ_n r_{A,B}(n)
- Generated 2 follow-up open questions

### Key Mathematical Finding
When A, B have positive lower density δ (cA(N) ≥ δN), the new bound gives:
Σ_{n≤N} r_{A,B}(n) ≥ cA(N/2)·cB(N/2) ≥ (δN/2)² = δ²N²/4
Average r_{A,B}(n) over [1,N] ≥ δ²N/4 → ∞
This proves the Erdős-Sárközy conjecture in the POSITIVE DENSITY CASE unconditionally.

### Files Modified
- `proofs/Proofs/Erdos1145Problem.lean` (+54 lines, now 737)

### Next Steps
- Formalize the positive-density corollary as a standalone theorem
- Consider OQ-01 (positive density case) as a new research problem
