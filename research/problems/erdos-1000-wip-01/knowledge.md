# Research Knowledge: erdos-1000-wip-01

## Problem
Complete Erdős #1000: Generalized Totients and Diophantine Approximation.
The existing formalization has 4 axioms (erdos_no_zero_limit, erdos_dichotomy, cassels_liminf_zero, haight_resolution) and 0 sorries. Goal: prove one or more axioms.

## Summary
Proved 2 new structural lemmas that establish the fundamental lower bound connecting generalized totients to Euler's totient function. Fixed Mathlib API migration issues.

## Session 2026-03-25 (Session 1) - Structural Lower Bound

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Proved `phiA_ge_totient`: φ_A(k) ≥ φ(n_k) for any increasing sequence A
  - Key insight: coprime elements always pass the phiA filter
  - If gcd(m, n_k) = 1, then reducedDenom m n_k = n_k > n_j for all j < k
  - Proof: subset argument — (range n).filter(Coprime n) ⊆ (Icc 1 n).filter(phiA_cond)
  - k=0 case: phiA_zero gives phiA = n₀ ≥ totient(n₀)
  - k≥1 case: n_k ≥ 2, so the subset injection works
- Proved `densityRatio_ge_totient_ratio`: ρ_A(k) ≥ φ(n_k)/n_k
  - Direct corollary of phiA_ge_totient via div_le_div_of_nonneg_right
- Fixed Mathlib API migration issues in existing proofs:
  - `∑ k in range N` → `∑ k ∈ range N` (3 instances)
  - `strictMono` proof: `by omega` → `Nat.add_lt_add_right`
  - Constructor syntax: restructured `⟨by ..., by ...⟩` to `refine ⟨?_, ...⟩`
  - `simp at hg; omega` → `simp at hg` (simp now closes goal)
  - `push_cast; linarith` → explicit cast + linarith
  - `le_div_iff₀` rewrite → explicit mul_div_cancel approach

### Key Findings
- The lower bound φ_A(k) ≥ φ(n_k) is necessary but NOT sufficient for erdos_no_zero_limit
  - φ(n_k)/n_k CAN go to 0 (e.g., primorial sequence)
  - Erdős' proof must use deeper structural arguments about the counting
- The Mathlib API has diverged from when this file was written (v4.26.0)
  - `∑ ... in` syntax replaced by `∑ ... ∈`
  - Division lemma naming changed
  - omega behavior with semiimplicit binders changed

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 2 new theorems + migration fixes (304→370 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated counts and sections

### Next Steps
- Investigate `cassels_liminf_zero`: simplest axiom to prove? Needs explicit sequence construction
- Investigate `erdos_no_zero_limit`: needs understanding of WHY ρ_A can't converge to 0 despite φ(n_k)/n_k → 0. Likely needs structural argument about the excluded denominators
- The lower bound enables future work: any proof of `erdos_no_zero_limit` will use `phiA_ge_totient` as a foundation
