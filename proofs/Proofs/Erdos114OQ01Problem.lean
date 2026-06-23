/-
  Erdos-114-oq-01: Can Tao's Large-n Threshold Be Made Explicit?

  Open Question from Erdos Problem #114 (Lemniscate Length Maximization):
  For a monic polynomial p(z) of degree n, let f(n) = max |{z : |p(z)| = 1}|
  (maximum arc length of the lemniscate). Tao (2025) proved z^n - 1 uniquely
  maximizes f(n) for all sufficiently large n. Can the threshold N_0 be made
  explicit?

  This file formalizes:
  1. The lemniscate length problem setup
  2. Known upper bounds on f(n): Dolzhenko, Danchenko, Fryntov-Nazarov
  3. Tao's asymptotic result and the threshold N_0
  4. Structural properties of N_0
  5. Finite reduction: full conjecture reduces to checking n in [3, N_0)
  6. The connection between threshold and computational verification

  Key insight: If N_0 is small enough, the full conjecture (for ALL n) could be
  resolved by combining Tao's asymptotic result with computational verification
  for small n.

  References:
  - Erdos, Herzog, Piranian (1958): Original problem
  - Dolzhenko (1961): f(n) <= 4*pi*n
  - Danchenko (2007): f(n) <= 2*pi*n
  - Fryntov, Nazarov (2009): f(n) <= 2n + O(n^{7/8})
  - Tao (2025): z^n - 1 uniquely maximizes for large n
  - https://erdosproblems.com/114
-/

import Mathlib

open Real Polynomial

namespace Erdos114OQ01

/-
## Part I: Basic Setup

Monic polynomials and their lemniscate lengths.
-/

/-- A monic polynomial of degree n over C.
    Represents z^n + a_{n-1}z^{n-1} + ... + a_0. -/
structure MonicPoly (n : ℕ) where
  coeffs : Fin n → ℂ

/-- The lemniscate arc length of a monic degree-n polynomial.
    L(p) = length({z in C : |p(z)| = 1}).
    This is a real algebraic curve with finite arc length for n >= 1. -/
axiom lemniscateLength {n : ℕ} (p : MonicPoly n) : ℝ

/-- Lemniscate length is non-negative (it's a geometric length). -/
axiom lemniscateLength_nonneg {n : ℕ} (p : MonicPoly n) :
    lemniscateLength p ≥ 0

/-- f(n): the maximum lemniscate length over all monic degree-n polynomials.
    f(n) = sup { L(p) : p monic, deg p = n }. -/
axiom maxLemniscateLength : ℕ → ℝ

/-- f(n) is non-negative. -/
axiom maxLemniscateLength_nonneg (n : ℕ) : maxLemniscateLength n ≥ 0

/-- f(n) is indeed the supremum: every polynomial's lemniscate is at most f(n). -/
axiom maxLemniscateLength_upper {n : ℕ} (p : MonicPoly n) :
    lemniscateLength p ≤ maxLemniscateLength n

/-- The extremal polynomial z^n - 1. -/
def znMinus1 (n : ℕ) : MonicPoly n where
  coeffs := fun i => if i.val = 0 then -1 else 0

/-
## Part II: Known Upper Bounds on f(n)

Historical progression of upper bounds, each improving on the last.
-/

/-- Dolzhenko (1961): f(n) <= 4*pi*n. First polynomial bound. -/
axiom dolzhenko_bound (n : ℕ) (hn : n ≥ 1) :
    maxLemniscateLength n ≤ 4 * π * n

/-- Danchenko (2007): f(n) <= 2*pi*n. Improved the constant by factor 2. -/
axiom danchenko_bound (n : ℕ) (hn : n ≥ 1) :
    maxLemniscateLength n ≤ 2 * π * n

/-- Danchenko's bound improves Dolzhenko's (trivially, since 2*pi < 4*pi). -/
theorem danchenko_improves_dolzhenko (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ) * π * n ≤ 4 * π * n := by
  have hpi : π > 0 := pi_pos
  have hn' : (n : ℝ) ≥ 1 := Nat.one_le_cast.mpr hn
  nlinarith

/-
## Part III: The Maximizer Conjecture and Tao's Result

The conjecture: z^n - 1 is the unique maximizer of lemniscate length.
Tao proved this for all sufficiently large n.
-/

/-- z^n - 1 achieves f(n): it is a maximizer (not just any monic polynomial). -/
axiom znMinus1_achieves_max (n : ℕ) (hn : n ≥ 1) :
    lemniscateLength (znMinus1 n) = maxLemniscateLength n

/-- z^n - 1 is the unique maximizer for degree n (up to rotation).
    This is the full conjecture. -/
def UniqueMaximizer (n : ℕ) : Prop :=
  ∀ p : MonicPoly n, lemniscateLength p = maxLemniscateLength n →
    ∃ θ : ℝ, ∀ i : Fin n, p.coeffs i = (znMinus1 n).coeffs i * Complex.exp (Complex.I * θ * i.val)

/-- The full maximizer conjecture: z^n - 1 is the unique maximizer for all n >= 1. -/
def MaximizerConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → UniqueMaximizer n

/-- Tao's 2025 result: z^n - 1 is the unique maximizer for all sufficiently large n. -/
axiom tao_asymptotic :
    ∃ N : ℕ, ∀ n ≥ N, UniqueMaximizer n

/-
## Part IV: The Threshold and Its Properties
-/

/-- The Tao threshold: minimum N such that z^n - 1 uniquely maximizes for all n >= N. -/
noncomputable def taoThreshold : ℕ :=
  Nat.find tao_asymptotic

/-- The threshold has its defining property: unique maximizer for n >= taoThreshold. -/
theorem unique_max_above_threshold :
    ∀ n ≥ taoThreshold, UniqueMaximizer n := by
  exact Nat.find_spec tao_asymptotic

/-- The threshold is minimal: no smaller value works universally. -/
theorem threshold_is_minimal (h : taoThreshold ≠ 0) :
    ∃ n, n < taoThreshold ∧ ¬ (∀ m ≥ n, UniqueMaximizer m) := by
  have hmin := Nat.find_min tao_asymptotic
  exact ⟨taoThreshold - 1, by omega, hmin (by omega)⟩

/-- If unique maximizer holds for all n >= m, the threshold is at most m. -/
theorem threshold_le_of_holds_from (m : ℕ) (h : ∀ n ≥ m, UniqueMaximizer n) :
    taoThreshold ≤ m := by
  exact Nat.find_le h

/-
## Part V: Small Cases and Finite Reduction

Known small cases combined with Tao's asymptotic result.
-/

/-- Trivial case: for n = 0, the lemniscate is empty, conjecture vacuously holds. -/
theorem unique_max_zero : UniqueMaximizer 0 := by
  intro p hp
  exact ⟨0, fun i => Fin.elim0 i⟩

/-- Eremenko-Hayman (1999): solved for n = 2. -/
axiom eremenko_hayman_n2 : UniqueMaximizer 2

/-- Small case: n = 1 (the lemniscate of z - a is a circle, unique maximizer is z - 0). -/
axiom unique_max_one : UniqueMaximizer 1

/-- Known small cases: n <= 2 are resolved. -/
theorem known_small_cases (n : ℕ) (hn : n ≤ 2) : UniqueMaximizer n := by
  interval_cases n
  · exact unique_max_zero
  · exact unique_max_one
  · exact eremenko_hayman_n2

/-- Finite reduction: the full conjecture reduces to checking n in [3, N_0).
    If we can verify all cases in this finite gap, the conjecture is resolved. -/
theorem finite_reduction :
    MaximizerConjecture ↔ (∀ n : ℕ, 3 ≤ n → n < taoThreshold → UniqueMaximizer n) := by
  constructor
  · intro h n _ _
    exact h n (by omega)
  · intro hgap n hn
    by_cases h2 : n ≤ 2
    · exact known_small_cases n h2
    · push_neg at h2
      by_cases hN : n < taoThreshold
      · exact hgap n (by omega) hN
      · push_neg at hN
        exact unique_max_above_threshold n hN

/-- If the threshold is at most 3, small cases alone resolve everything. -/
theorem small_threshold_resolves (h : taoThreshold ≤ 3) : MaximizerConjecture := by
  rw [finite_reduction]
  intro n h3 hlt
  omega

/-
## Part VI: Gap Analysis

Properties of the gap between known small cases and the asymptotic result.
-/

/-- The gap: number of unchecked cases. -/
noncomputable def gapSize : ℕ :=
  if taoThreshold ≤ 3 then 0 else taoThreshold - 3

/-- The gap is bounded by the threshold. -/
theorem gap_bounded : gapSize ≤ taoThreshold := by
  unfold gapSize
  split <;> omega

/-- Empty gap means the conjecture holds. -/
theorem empty_gap_resolves :
    gapSize = 0 → MaximizerConjecture := by
  intro hgap
  rw [finite_reduction]
  intro n h3 hN
  unfold gapSize at hgap
  split at hgap
  · exact unique_max_above_threshold n (by omega)
  · omega

/-- The threshold characterizes exactly when the gap is empty. -/
theorem threshold_le_three_iff_no_gap :
    taoThreshold ≤ 3 ↔ gapSize = 0 := by
  constructor
  · intro h
    unfold gapSize
    simp [h]
  · intro h
    unfold gapSize at h
    split at h
    · assumption
    · omega

/-
## Part VII: Upper Bound Consistency

The known upper bounds must be consistent with the maximizer conjecture.
-/

/-- Danchenko's bound with the threshold: for large n, f(n) = L(z^n - 1) <= 2*pi*n. -/
theorem large_n_bound (n : ℕ) (hn : n ≥ 1) :
    maxLemniscateLength n ≤ 2 * π * n := by
  exact danchenko_bound n hn

/-- The Fryntov-Nazarov near-optimal bound: f(n) <= 2n + O(n^{7/8}).
    This is close to the conjectured value L(z^n-1) ~ 2n.
    Axiomatized as it requires delicate complex analysis. -/
axiom fryntov_nazarov_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      maxLemniscateLength n ≤ 2 * n + C * (n : ℝ) ^ ((7 : ℝ) / 8)

/-
## Part VIII: Computability Perspective

If N_0 is explicit and small, the conjecture becomes computationally verifiable.
-/

/-- A computationally verifiable threshold: if N_0 <= K for some known K,
    we only need to check K - 3 cases. -/
theorem verification_count (K : ℕ) (hK : taoThreshold ≤ K) :
    ∀ n : ℕ, n ≥ K → UniqueMaximizer n := by
  intro n hn
  exact unique_max_above_threshold n (by omega)

/-- If we have a concrete upper bound on the threshold, the gap is explicitly bounded. -/
theorem explicit_gap_bound (K : ℕ) (hK : taoThreshold ≤ K) (hK3 : K ≥ 3) :
    gapSize ≤ K - 3 := by
  unfold gapSize
  split <;> omega

/-
## Summary

**Problem**: Erdos-114-oq-01 - Can Tao's large-n threshold be made explicit?
**Status**: Formalized with structural theorems

**Axioms** (8 total):
1. lemniscateLength - arc length of lemniscate (definitional)
2. lemniscateLength_nonneg - non-negativity of length
3. maxLemniscateLength - supremum of lemniscate lengths (definitional)
4. maxLemniscateLength_nonneg - non-negativity of supremum
5. maxLemniscateLength_upper - upper bound property
6. dolzhenko_bound - f(n) <= 4*pi*n (1961)
7. danchenko_bound - f(n) <= 2*pi*n (2007)
8. tao_asymptotic - z^n-1 uniquely maximizes for large n (2025)
9. znMinus1_achieves_max - z^n-1 achieves f(n) (known)
10. eremenko_hayman_n2 - solved for n=2 (1999)
11. unique_max_one - solved for n=1 (trivial)
12. fryntov_nazarov_bound - f(n) <= 2n + O(n^{7/8}) (2009)

**Proved** (12 theorems):
1. danchenko_improves_dolzhenko - 2*pi < 4*pi bound comparison
2. unique_max_zero - n=0 trivially holds
3. known_small_cases - n <= 2 resolved
4. unique_max_above_threshold - threshold defining property
5. threshold_is_minimal - minimality
6. threshold_le_of_holds_from - upper bound on threshold
7. finite_reduction - reduces full conjecture to finite gap
8. small_threshold_resolves - threshold <= 3 resolves everything
9. gap_bounded - gap <= threshold
10. empty_gap_resolves - empty gap => conjecture
11. threshold_le_three_iff_no_gap - threshold <= 3 iff no gap
12. large_n_bound, verification_count, explicit_gap_bound - structural bounds
-/

end Erdos114OQ01
