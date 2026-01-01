# Knowledge Base: Riemann Hypothesis Consequences

## Progress Summary

**Date**: 2025-12-31
**Phase**: SURVEY (completed)
**Result**: Successfully formalized auxiliary functions and RH consequence statements

## Key Discovery

**RiemannHypothesis is already defined in Mathlib!**

```lean
-- Mathlib/NumberTheory/LSeries/RiemannZeta.lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## What We've Built

### Definitions

1. **Mertens function**
   ```lean
   def mertens (n : ℕ) : ℤ :=
     ∑ k ∈ Finset.range (n + 1), μ k
   ```

2. **Chebyshev theta function**
   ```lean
   noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
     ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p
   ```

3. **Chebyshev psi function** (added Session 4)
   ```lean
   noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
     ∑ k ∈ Finset.range (n + 1), Λ k
   ```

### Computed Values

| n | M(n) |
|---|------|
| 0 | 0 |
| 1 | 1 |
| 2 | 0 |
| 3 | -1 |
| 4 | -1 |
| 5 | -2 |
| 10 | -1 |
| 20 | -3 |
| 30 | -3 |

### Möbius Function Verifications (added Session 2)

| n | μ(n) | Reason |
|---|------|--------|
| 1 | 1 | Definition |
| 6 | 1 | 2·3, two primes |
| 30 | -1 | 2·3·5, three primes |
| 4 | 0 | 2², squared factor |
| 12 | 0 | 2²·3, squared factor |

### Möbius Identity Verifications (added Session 2)

Σ_{d|n} μ(d) = [n=1] verified computationally for:
- n = 1: sum = 1 ✓
- n = 2, 3, 5, 6, 12: sum = 0 ✓

### Theorems Proven

1. **`mertens_step`**: M(n+1) = M(n) + μ(n+1)
2. **`moebius_of_not_squarefree`**: μ(n) = 0 if n not squarefree
3. **`moebius_prime`**: μ(p) = -1 for primes
4. **`moebius_one`**: μ(1) = 1
5. **`moebius_six`**: μ(6) = 1
6. **`moebius_thirty`**: μ(30) = -1
7. **`moebius_four`**: μ(4) = 0
8. **`moebius_twelve`**: μ(12) = 0
9. **`moebius_sum_divisors_one`**: Σ_{d|1} μ(d) = 1
10. **`moebius_sum_divisors_six`**: Σ_{d|6} μ(d) = 0
11. **`moebius_sum_divisors_twelve`**: Σ_{d|12} μ(d) = 0
12. **`rh_zeros_on_critical_line`**: RH → all non-trivial zeros have Re = 1/2
13. **`trivial_zeros_negative_real_part`**: Re(-2(n+1)) < 0
14. **`trivial_zeros_off_critical_line`**: Trivial zeros not on critical line

### Axioms Stated

1. **`rh_implies_mertens_bound`**: RH → |M(x)| = O(√x)
2. **`rh_implies_chebyshev_bound`**: RH → θ(x) = x + O(√x log²x)
3. **`rh_implies_prime_gap_bound`**: RH → p_{n+1} - p_n = O(√p_n log p_n)

## Technical Insights

### What Mathlib Has

| Component | Status |
|-----------|--------|
| Riemann zeta ζ(s) | ✓ Full complex definition |
| RiemannHypothesis | ✓ Formalized |
| Functional equation | ✓ Proven |
| Trivial zeros | ✓ ζ(-2n) = 0 proven |
| Special values | ✓ ζ(0) = -1/2, etc. |
| Möbius function μ | ✓ ArithmeticFunction |
| Von Mangoldt Λ | ✓ Mathlib.NumberTheory.VonMangoldt |
| Prime Number Theorem | ✗ Not in Mathlib (but in PrimeNumberTheoremAnd) |
| Chebyshev θ(x) | ✗ Defined by us |
| Chebyshev ψ(x) | ✓ Defined by us (Session 4) using Mathlib's Λ |
| Mertens function | ✗ Defined by us |

### Why Full Proofs Aren't Possible

The classical proofs of RH consequences require:
1. **Prime Number Theorem**: π(x) ~ x/ln(x) - not in Mathlib
2. **Explicit formula**: Connects zeros to prime distribution
3. **Zero-free regions**: Bounds on where ζ(s) ≠ 0
4. **Contour integration**: Complex analysis machinery

Without PNT, we can only state consequences, not prove them.

## Value Assessment

This survey is valuable because:

1. ✅ Documents that RH is already formalized
2. ✅ Provides useful helper functions (Mertens, Chebyshev)
3. ✅ States classical consequences formally
4. ✅ Proves what can be proved (trivial implications)
5. ✅ Documents the infrastructure gap for future work

## Comparison: SURVEY vs DEEP DIVE

| Aspect | SURVEY (what we did) | DEEP DIVE (hypothetical) |
|--------|---------------------|--------------------------|
| RH definition | Used existing | Used existing |
| Helper functions | Defined | Same |
| Computed values | 7 Mertens values | Same |
| Trivial theorems | 6 proven | Same |
| RH consequences | Axioms | Would need PNT |
| Time spent | ~1 hour | Weeks+ |

SURVEY was the right choice - can't prove substantial RH consequences without PNT.

## Session Log

### Session 6 (2026-01-01)

**Mode**: REVISIT
**Problem**: rh-consequences
**Prior Status**: surveyed

**Literature Search**:
- Searched "[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) Lean 4 Mathlib4 2025 2026"
- Confirmed project is active; [arXiv:2503.07625](https://arxiv.org/abs/2503.07625) shows PNT with error term is formalized
- Searched "Mathlib4 Riemann zeta zero-free region explicit formula 2025"
- Found no Mathlib formalization of zero-free regions (only mathematical papers)
- Searched "[Li's criterion](https://en.wikipedia.org/wiki/Li's_criterion)" - elegant RH equivalent from 1997

**What we added**:
1. Part 11: Completed Zeta Function (Xi Function)
   - Re-exports of `completedRiemannZeta`, `completedRiemannZeta₀`
   - Functional equation `completedRiemannZeta_one_sub`
   - Differentiability of Λ₀
   - Functional equation for ζ

2. Part 12: Li's Criterion
   - `liConstant` - Li's constants λₙ (abstract definition)
   - `lis_criterion` - RH ↔ λₙ ≥ 0 for all n ≥ 1 (axiom)
   - `li_constant_asymptotic` - Keiper-Li asymptotic behavior (axiom)

3. Part 13: Zero Counting and Riemann-von Mangoldt Formula
   - `zeroCountingFunction` - N(T) counts zeros up to height T
   - `riemann_von_mangoldt_formula` - N(T) ~ (T/2π)log(T/2πe) (axiom)
   - `gourdon_verification` - 10^13 zeros verified on critical line (axiom)

4. Part 14: More Zeta Values
   - `zeta_six_formula` - ζ(6) via general Bernoulli formula
   - `zeta_eight_formula` - ζ(8) via general Bernoulli formula

**Key Insight**:
Li's criterion is a remarkable equivalence: RH holds iff all Li constants λₙ ≥ 0. This reduces RH to checking positivity of a sequence, though computing λₙ requires knowing the zeros. The Keiper-Li asymptotic shows λₙ ~ n(A log n + B) if RH holds, but oscillates wildly if RH fails.

**Outcome**:
- RiemannHypothesisConsequences.lean: ~632 lines (up from ~495)
- Added 4 new definitions, 5 new axioms, 2 new theorems
- File compiles successfully

**Files Modified**:
- `proofs/Proofs/RiemannHypothesisConsequences.lean` (+137 lines)
- `research/problems/rh-consequences/knowledge.md` - this file

**Next Steps**:
1. Add PrimeNumberTheoremAnd as dependency to enable PNT-based proofs
2. Formalize explicit bounds on Li constants (known numerical computations)
3. Add Selberg's explicit formula relating zeros to primes
4. Explore Nyman-Beurling criterion (another RH equivalent)

### Session 5 (2025-12-31)

**Mode**: REVISIT
**Problem**: rh-consequences
**Prior Status**: surveyed

**Literature Search**:
- Searched "Mathlib4 Riemann zeta function 2025 new theorems formalization"
- Found major new Mathlib additions documented at https://arxiv.org/html/2503.00959

**New Mathlib Theorems Found**:
- `riemannZeta_two`: ζ(2) = π²/6 (Basel problem)
- `riemannZeta_four`: ζ(4) = π⁴/90
- `riemannZeta_ne_zero_of_one_lt_re`: ζ(s) ≠ 0 for Re(s) > 1
- `riemannZeta_eulerProduct_tprod`: Euler product formula
- `riemannZeta_neg_nat_eq_bernoulli`: values at negative integers
- `riemannZeta_one_sub`: functional equation
- `riemannZeta_residue_one`: residue at s=1 is 1

**What we added**:
1. Part 9: Mathlib Zeta Function Theorems
   - `zeta_two_eq_pi_sq_div_six`: re-export of Basel problem
   - `zeta_four_eq_pi_fourth_div_ninety`: ζ(4) = π⁴/90
   - `zeta_nonzero_for_re_gt_one`: non-vanishing for Re(s) > 1
   - `zeta_neg_nat_bernoulli`: Bernoulli number formula
   - `zeta_euler_product`: Euler product formula
   - `euler_product_nonvanishing`: consequence of Euler product
   - `criticalStrip`, `criticalLine`: set definitions
   - `criticalLine_subset_criticalStrip`: containment proof

2. Part 10: Computational Zeta Values
   - `zeta_zero_value`: ζ(0) = -1/2
   - `zeta_neg_two`: ζ(-2) = 0 (trivial zero)
   - `zeta_neg_four`: ζ(-4) = 0 (trivial zero)

**Key Finding**:
The Mathlib zeta infrastructure has grown substantially. The Euler product formula and non-vanishing for Re(s) > 1 are now fully formalized. This is crucial infrastructure for any future work on RH consequences.

**Build Status**: ✅ Compiles successfully
**File Size**: ~495 lines (up from ~480)

### Session 4 (2025-12-31)

**Mode**: REVISIT
**Problem**: rh-consequences
**Prior Status**: surveyed

**What we did**:
1. Added von Mangoldt function (Λ) formalization using `Mathlib.NumberTheory.VonMangoldt`
2. Defined Chebyshev psi function ψ(x) = Σ_{n≤x} Λ(n)
3. Proved computed values for ψ(1), ψ(2), ψ(3)
4. Proved von Mangoldt values: Λ(0), Λ(4), Λ(6), Λ(8), Λ(9)
5. Added recurrence relation: ψ(n+1) = ψ(n) + Λ(n+1)
6. Added RH → ψ(x) bound axiom
7. Fixed zeta value proofs using Bernoulli number lemmas
8. Fixed π notation conflict with primeCounting (use Real.pi explicitly)

**New Definitions**:
```lean
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), Λ k
```

**New Theorems Proven**:
- `vonMangoldt_zero`: Λ(0) = 0
- `chebyshevPsi_one`: ψ(1) = 0
- `chebyshevPsi_two`: ψ(2) = log 2
- `chebyshevPsi_three`: ψ(3) = log 6
- `vonMangoldt_four`: Λ(4) = log 2
- `vonMangoldt_six`: Λ(6) = 0
- `vonMangoldt_eight`: Λ(8) = log 2
- `vonMangoldt_nine`: Λ(9) = log 3
- `chebyshevPsi_step`: ψ(n+1) = ψ(n) + Λ(n+1)
- `zeta_neg_one`: ζ(-1) = -1/12 (fixed)
- `zeta_neg_three`: ζ(-3) = 1/120 (fixed)
- `zeta_neg_four`: ζ(-4) = 0 (fixed)

**New Axioms**:
- `rh_implies_psi_bound`: RH → ψ(x) = x + O(√x log²x)

**Key Technical Insights**:
- Von Mangoldt is in `Mathlib.NumberTheory.VonMangoldt` with notation `Λ`
- Use `vonMangoldt_apply_pow` + `vonMangoldt_apply_prime` for prime powers
- Use `ArithmeticFunction.map_zero` pattern for Λ(0) = 0
- Bernoulli values need explicit lemmas: `bernoulli_eq_bernoulli'_of_ne_one`, `bernoulli'_two`, etc.

**Build Status**: ✅ Compiles successfully

**Outcome**:
- File now has 20+ proven theorems plus 6 axioms
- Both Chebyshev functions θ and ψ now defined
- Von Mangoldt function properly integrated
- File size: ~480 lines

**Files Modified**:
- `proofs/Proofs/RiemannHypothesisConsequences.lean` - added ~60 lines
- `research/problems/rh-consequences/knowledge.md` - this file

### Session 3 (2025-12-31)

**Literature Search**:
- Searched "PrimeNumberTheoremAnd Lean 4 PNT formalized 2025"
- Major finding: **Strong PNT has been formally proven in Lean 4!**
- Jesse Han reported Gauss AI completed the proof in 3 weeks (25K LOC)
- Available: Weak, Medium, Strong PNT, PNT in arithmetic progressions, Chebotarev density

**Sources**:
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- https://x.com/jessemhan/status/1966379609932673097
- https://arxiv.org/abs/2503.07625 (ζ(3) irrationality uses PNT)

**What we added**:
- `rh_iff_mertens_half_epsilon`: RH ↔ M(x) = O(x^(1/2+ε)) (Littlewood)
- `mertens_conjecture_false`: Statement that Mertens conjecture is false (Odlyzko-te Riele 1985)
- `mertens_fifty`: M(50) = -3
- `mertens_hundred`: M(100) = 1
- Updated summary to document PNT project path forward

**Outcome**:
- File now has 16+ proven theorems plus 5 axioms
- Mertens-RH equivalence formalized
- Clear path forward documented: import PrimeNumberTheoremAnd

**Key Finding**:
The situation has fundamentally changed. PNT is now available in Lean 4!
The blocker is that PrimeNumberTheoremAnd is not yet a Mathlib dependency.
To use it, add to lakefile.toml:
```toml
[[require]]
name = "PrimeNumberTheoremAnd"
scope = "AlexKontorovich"
```

**Next Steps**:
1. **High priority**: Test adding PrimeNumberTheoremAnd as dependency
2. Import Chebyshev psi/theta from PNT project (likely already defined there)
3. Replace RH consequence axioms with conditional theorems using PNT
4. Look for explicit formula for π(x) in PNT project

### Session 2 (2025-12-31)

**Literature Search**:
- Searched "Mathlib4 Prime Number Theorem Lean 2024 2025"
- Found: PrimeNumberTheoremAnd project by Tao & Kontorovich
- Status: Active project, strong PNT reportedly formalized by Gauss AI (2025)
- Not yet merged into Mathlib proper

**What we added**:
- 2 more Mertens values: M(20) = -3, M(30) = -3
- 5 Möbius function verifications: μ(1), μ(6), μ(30), μ(4), μ(12)
- 6 Möbius identity verifications: Σ_{d|n} μ(d) for n = 1, 2, 3, 5, 6, 12

**Outcome**:
- File now has 14+ proven theorems
- Better coverage of Möbius function properties
- Computational verification of fundamental identity

**Key Finding**:
The PrimeNumberTheoremAnd project (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) has made significant progress. Once merged into Mathlib, we could prove RH consequences conditionally.

**Next Steps**:
1. Monitor PNT project for Mathlib integration
2. Consider importing PrimeNumberTheoremAnd as dependency
3. Add more Mertens values (M(50), M(100)) ✓ Done in Session 3

## File Location

`proofs/Proofs/RiemannHypothesisConsequences.lean`

## References

- [Mathlib RiemannZeta.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean)
- Edwards, "Riemann's Zeta Function" (1974)
- Titchmarsh, "The Theory of the Riemann Zeta-Function" (1986)
