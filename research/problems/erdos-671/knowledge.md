# Erdős Problem #671 — Lagrange Interpolation Convergence

**Status**: `in-progress` (ACT phase)
**Prize**: $250 open problem
**Source**: https://erdosproblems.com/671

## Problem Summary

Can Lagrange interpolation converge pointwise at a point x where the Lebesgue function
λ_n(x) = Σ|p_i^n(x)| diverges (limsup → ∞)?

- **Question 1**: ∃ point sequence where for every continuous f, ∃ x with limsup λ_n(x) = ∞ yet L^n f(x) → f(x)?
- **Question 2**: Same but limsup λ_n(x) = ∞ for ALL x ∈ [-1,1]?

**Known**: Bernstein (1931): ∃ x₀ with limsup λ_n(x₀) = ∞ for any sequence.
**Known**: Erdős-Vértesi (1980): ∃ continuous f with |L^n f(x)| → ∞ a.e. for any sequence.

## Session 2026-05-04 (Session 1) — Initial formalization

**Mode**: FRESH (new gallery entry)
**Outcome**: progress (4 sorries eliminated, compilation fixes)

### What I Did

- Located `proofs/Proofs/Erdos671Problem.lean` with 23 real sorries
- Fixed bad `import` statements (specific module paths → `import Mathlib`)
- Proved `lagrangeBasis_self`: `∏ j ≠ i, (1/(a_i-a_j))*(a_i-a_j) = 1` via `Finset.prod_eq_one` + `field_simp`
- Proved `lagrangeBasis_other`: factor `a_j - a_j = 0` gives product = 0 via `Finset.prod_eq_zero`
- Proved `lagrangeInterp_at_node`: isolate the i-th term via `Finset.sum_eq_single_of_mem`
- Proved `chebyshevNodes.in_interval`: `Real.cos_mem_Icc _` (one-liner)
- Fixed syntax `∏ j in s` → `∏ j ∈ s` (deprecated in current Mathlib)
- Fixed `Filter.limsup ... = ⊤` type error: ℝ has no Top; use EReal cast `(f n : EReal)`
- Fixed `lagrangeInterp f` type mismatch: changed `f : ℝ → ℝ` to `f : Set.Icc (-1:ℝ) 1 → ℝ` so `C([-1,1], ℝ)` coerces automatically
- PR #15444 created and updated

### Key Findings

- `∏ j in s, ...` syntax deprecated; use `∏ j ∈ s, ...`
- `Filter.limsup (f : ℕ → ℝ) atTop : ℝ` but `⊤ : ℝ` doesn't typecheck (ℝ has no Top); use `(· : EReal)` cast
- `C(Set.Icc (-1:ℝ) 1, ℝ)` coerces to `Set.Icc (-1:ℝ) 1 → ℝ` via DFunLike automatically
- Lagrange basis proof strategy: prod = 1 via each factor = 1 (distinctness gives non-zero denominator); prod = 0 via finding one zero factor

### Files Modified

- `proofs/Proofs/Erdos671Problem.lean` (main file)
- `src/data/proofs/erdos-671/meta.json` (sorries 23→19)

### Remaining Sorries (19)

- `lagrangeBasis_self`, `lagrangeBasis_other`, `lagrangeInterp_at_node`: **PROVED**
- `chebyshevNodes.in_interval`: **PROVED**
- `lagrangeInterp_degree`: degree bound for Lagrange interpolant (HARD)
- `lebesgueFunction_ge_one`: λ_n ≥ 1 at nodes (HARD — needs partition of unity argument)
- `bernstein`: Bernstein's 1931 theorem (HARD — needs Baire category or explicit construction)
- `lebesgueConstant_growth`: Λ_n ≥ (2/π)ln(n) - 1 (HARD)
- `erdos_vertesi`: Erdős-Vértesi 1980 theorem (HARD)
- `question1_open` / `question2_open`: axioms (OPEN)
- `chebyshevNodes.distinct`: injectivity of cos on specific points (HARD)
- `equidistantNodes` (2 sorries): arithmetic bounds (MODERATE)
- `equidistant_diverges`: exponential Lebesgue constant for equidistant nodes (HARD)
- `faber`: Faber's theorem (HARD)
- `positive_measure_divergence`, `full_measure_convergence`: measure-theoretic (HARD)
- `main_conjecture_open`: axiom (OPEN)
- `q2_implies_q1`, `q2_fails_implies`: logical implications (MODERATE — should follow from defs)

### Next Steps

1. Try `q2_implies_q1`: should follow directly from definitions (Q2 is strictly stronger than Q1)
2. Try `lebesgueFunction_ge_one`: use partition of unity; Σ p_i(x) = 1 (interpolating constants) so |Σ p_i(x)| ≤ Σ|p_i(x)|
3. Try `lagrangeInterp_degree`: use that lagrangeBasis has degree ≤ n-1 and the sum has ≤ n terms
4. Submit `bernstein`, `lebesgueConstant_growth`, `erdos_vertesi` to Aristotle as HARD sorries
