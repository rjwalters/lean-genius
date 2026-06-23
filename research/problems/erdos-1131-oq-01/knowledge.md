# Erdős Problem #1131 OQ-01: Lagrange Basis Polynomial Integrals

## Problem Summary

For x₁,...,xₙ ∈ [-1,1], define Lagrange basis polynomials l_k(x) = ∏_{i≠k} (x - xᵢ)/(xₖ - xᵢ).
Find the minimum of I(x₁,...,xₙ) = ∫₋₁¹ Σₖ |l_k(x)|² dx.
Conjecture: min I = 2 - (1+o(1))/n.

## Current State
- **File**: `proofs/Proofs/Erdos1131Problem.lean` (1076 lines)
- **Sorries**: 0 — ALL PROVED
- **Axioms**: 1 (erdos_1131_conjecture — OPEN, must stay)
- **Theorems**: 14 public + private helpers, all proved
- **Phase**: COMPLETED (merged in commit 646d5ebe89, 2026-04-12)

## Session 2026-04-12 (Session 5) - Prove both remaining sorries

**Mode**: REVISIT (RICH knowledge, score 64)
**Outcome**: completed — 0 sorries, proof fully formalized

### What I Did
1. **Proved `chebyshev_interp`** (Lagrange interpolation exactness):
   - T_{j+1}(cos(arccos x)) = (Lagrange interpolant of T_{j+1} at Chebyshev nodes).eval x
   - LHS: T_{j+1}.eval x via `Polynomial.Chebyshev.T_real_cos` + `Real.cos_arccos`
   - RHS: `Lagrange.interpolate` evaluation identity (expand Polynomial.eval_finset_sum)
   - Uniqueness: `Lagrange.eq_interpolate` requires deg T_{j+1} = j+1 < n (since j ∈ range(n-1))
   - Degree: `Polynomial.Chebyshev.degree_T` gives deg = j+1, then cast bound closes it

2. **Proved `chebyshev_sq_expansion`** (bilinear DCT Parseval expansion):
   - Goal: n·∑l_k² = 1 + 2∑_j (∑_k cos(jθ_k)l_k)²
   - Used `dct_offdiag` (off-diagonal = 0) to reduce ∑_k∑_m to diagonal sum
   - Used `Finset.sum_mul_sum` to factorize inner double sums
   - Used `Finset.sum_comm` (k,m ↔ j,k,m) to rearrange to product of sums²
   - Used `partition_of_unity` for the constant term (∑l_k)² = 1

### Key Findings
- `Lagrange.eq_interpolate` requires explicit injectivity hypothesis (InjOn nodes univ)
- Degree of Chebyshev polynomial T m : ℤ → ℕ; `natAbs (j+1 : ℤ) = j+1` needs `simp`
- `Polynomial.eval_finset_sum` unwraps Lagrange.interpolate evaluation correctly
- Off-diagonal vanishing via `dct_offdiag` + `mul_zero` collapses the sum immediately

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (642→1076 lines, 2→0 sorries, 1 axiom remains)
- `src/data/proofs/erdos-1131/meta.json` (sorries: 0 confirmed)

### Next Steps
- Problem COMPLETE. Open conjecture (min I = 2-(1+o(1))/n) stays as axiom.
- Potential follow-up: sharp lower bound improvement — can the (log n)² factor in ESVV94's 2-O((log n)²/n) be removed?

## Session 2026-03-25 (Session 2) - Prove sorries, remove false axiom

**Mode**: REVISIT (MODERATE knowledge, score 12)
**Outcome**: progress

### What I Did
1. Proved `sum_sq_lagrangeBasis_ge` (∑ l_k² ≥ 1/n) via variance trick:
   - `suffices` to reduce to showing ∑l_k² - 1/n = ∑(l_k - 1/n)²
   - Expanded via `sub_sq`, split sum via `Finset.sum_add_distrib`/`sum_sub_distrib`
   - Factored middle sum via `Finset.mul_sum`, applied `hpou` (partition of unity)
   - Closed with `field_simp; ring`

2. Proved `lagrangeIntegral_lower_bound` (I ≥ 2/n) via integral monotonicity:
   - Showed integrand is continuous via `continuous_finset_sum` + `continuous_finset_prod`
   - Rewrote 2/n as ∫₋₁¹ 1/n dx
   - Used `intervalIntegral.integral_sub` + `intervalIntegral.integral_nonneg`

3. Removed false axiom `lagrangeIntegral_upper_bound` (I ≤ 2n):
   - **Counterexample**: n=2, nodes at 0 and δ give I = 2 + 4/(3δ²) → ∞ as δ → 0
   - No theorems depended on this axiom

### Key Findings
- `lagrangeIntegral_upper_bound` is mathematically false — no general upper bound on I exists
- `linarith` cannot recognize that `1/↑n` and `2/↑n` are linearly related; use `Finset.mul_sum` to factor first
- The `suffices` pattern (reduce goal to sum nonnegativity) is much cleaner than expanding and rearranging
- `field_simp; ring` handles the final arithmetic after clearing Finset.sum infrastructure

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (264→306 lines, 2→0 sorries, 3→2 axioms)
- `src/data/proofs/erdos-1131/meta.json`
- `src/data/research/problems/erdos-1131-oq-01.json`

### Next Steps
- `chebyshev_integral_estimate` requires Chebyshev polynomial T_n representation of l_k and exact integral computation — substantial infrastructure needed
- `erdos_1131_conjecture` is genuinely OPEN, stays as axiom

## Session 2026-03-24 (Session 3) - Factor exact formula, prove algebraic components

**Mode**: REVISIT (RICH knowledge, score 32)
**Outcome**: progress

### What I Did
1. **Proved `partial_fraction_sum`**: ∑1/(4(j+1)²-1) = m/(2m+1) by induction
2. **Proved `discrete_cosine_vanishing`**: ∑cos(rθ_k) = 0 via Abel summation + telescoping
3. **Proved `chebyshev_integral_exact`** from `chebyshev_integral_trace` + `partial_fraction_sum`
4. Added helpers: `two_sin_mul_cos`, `sin_nat_mul_pi`

### Key Findings
- `unfold_let` not valid in Lean 4.26.0 — use `simp only [hα_def]`
- `∑ k in ...` syntax invalid — use `∑ k ∈ ...`
- `positivity` needs explicit positivity hypotheses for Nat.cast
- `field_simp` needs denominators pre-normalized (rewrite `2*(n-1)+1` to `2*n-1` first)

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (365→467 lines, +5 proved lemmas)

### Next Steps
- Prove `chebyshev_integral_trace`: needs Chebyshev expansion + ∫T_j²dx
- `erdos_1131_conjecture` stays as axiom

## Session 2026-03-24 (Session 4) - Prove integration formula and trace combining step

**Mode**: REVISIT (RICH knowledge)
**Outcome**: major progress

### What I Did
1. **Proved `integral_chebyshev_sq`**: ∫₋₁¹ cos²(j·arccos x) dx = 1 - 1/(4j²-1)
   - Via cos²(jα) = (1+cos(2jα))/2, substitution x=cos θ, product-to-sum, FTC
2. **Proved 6 helper lemmas**: two_cos_mul_sin, integral_sin_mul, cos_nat_mul_pi, integral_cos_mul_sin, integral_cos_substitution, integral_chebyshev_sq
3. **Proved `chebyshev_integral_trace`** from chebyshev_sq_expansion + integral_chebyshev_sq
4. **Added `chebyshev_sq_expansion`** as sorry (DCT identity)

### Key Findings
- `Real.continuous_arccos` available in Mathlib
- `intervalIntegral.integral_comp_mul_deriv` for change of variables
- `Real.arccos_cos` requires 0 ≤ θ ∧ θ ≤ π
- `intervalIntegrable_finset_sum` and `intervalIntegral.integral_finset_sum` for sum/integral exchange

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (467→642 lines, sorry moved to expansion)

### Next Steps
- Prove `chebyshev_sq_expansion`: DCT identity (~200 lines)
- `erdos_1131_conjecture` stays as axiom
