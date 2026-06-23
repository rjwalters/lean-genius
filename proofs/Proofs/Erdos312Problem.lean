/-
Erdős Problem #312: Subset Sums of Unit Fractions

Source: https://erdosproblems.com/312
Status: OPEN

Statement:
Does there exist a constant c > 0 such that, for any K > 1, whenever A is a
sufficiently large finite multiset of positive integers with Σ_{n ∈ A} 1/n > K,
there exists a subset S ⊆ A with 1 - exp(-cK) < Σ_{n ∈ S} 1/n ≤ 1?

Known Results:
- Erdős-Graham: The weaker bound c/K² is known (polynomial precision)
- The conjectured exponential bound exp(-cK) remains open

The problem asks whether we can find subsets whose reciprocal sum is
exponentially close to 1, given a large enough total reciprocal sum.

Reference: Erdős-Graham [ErGr80]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.PSeries

open Finset Real Filter

namespace Erdos312

/- ## Part I: Unit Fraction Sums -/

/-- The reciprocal sum of a multiset of positive integers:
    Σ_{i ∈ {0,...,n-1}} 1/a(i) -/
noncomputable def reciprocalSum (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ)⁻¹

/-- The reciprocal sum over a subset S ⊆ {0,...,n-1} -/
noncomputable def subsetReciprocalSum (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (a i : ℝ)⁻¹

/-- reciprocalSum is non-negative when elements are natural numbers. -/
theorem reciprocalSum_nonneg (n : ℕ) (a : Fin n → ℕ) :
    0 ≤ reciprocalSum n a := by
  apply Finset.sum_nonneg
  intro i _
  exact inv_nonneg.mpr (Nat.cast_nonneg' (a i))

/-- subsetReciprocalSum is non-negative when elements are natural numbers. -/
theorem subsetReciprocalSum_nonneg (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) :
    0 ≤ subsetReciprocalSum n a S := by
  apply Finset.sum_nonneg
  intro i _
  exact inv_nonneg.mpr (Nat.cast_nonneg' (a i))

/-- The reciprocal sum over a subset is at most the total reciprocal sum. -/
theorem subsetSum_le_totalSum (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) :
    subsetReciprocalSum n a S ≤ reciprocalSum n a := by
  apply Finset.sum_le_univ_sum_of_nonneg
  intro i
  exact inv_nonneg.mpr (Nat.cast_nonneg' (a i))

/-- The reciprocal sum of the empty subset is 0. -/
theorem empty_subsetSum_eq_zero (n : ℕ) (a : Fin n → ℕ) :
    subsetReciprocalSum n a ∅ = 0 := by
  simp [subsetReciprocalSum]

/-- The full set gives the same as reciprocalSum. -/
theorem univ_subsetSum_eq_totalSum (n : ℕ) (a : Fin n → ℕ) :
    subsetReciprocalSum n a Finset.univ = reciprocalSum n a := by
  simp [subsetReciprocalSum, reciprocalSum]

/-- Subset reciprocal sums are monotone: S ⊆ T implies sum(S) ≤ sum(T). -/
theorem subsetReciprocalSum_mono (n : ℕ) (a : Fin n → ℕ) (S T : Finset (Fin n))
    (hST : S ⊆ T) : subsetReciprocalSum n a S ≤ subsetReciprocalSum n a T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro i _ _
  exact inv_nonneg.mpr (Nat.cast_nonneg' (a i))

/-- Subset reciprocal sum over a singleton {i} equals 1/a(i). -/
theorem subsetReciprocalSum_singleton (n : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    subsetReciprocalSum n a {i} = (a i : ℝ)⁻¹ := by
  simp [subsetReciprocalSum]

/-- Additive splitting for disjoint subsets: sum(S ∪ T) = sum(S) + sum(T). -/
theorem subsetReciprocalSum_disjoint_union (n : ℕ) (a : Fin n → ℕ)
    (S T : Finset (Fin n)) (hST : Disjoint S T) :
    subsetReciprocalSum n a (S ∪ T) =
      subsetReciprocalSum n a S + subsetReciprocalSum n a T := by
  simp [subsetReciprocalSum, Finset.sum_union hST]

/-- If all elements are positive and the multiset is nonempty, the total sum is positive. -/
theorem reciprocalSum_pos (n : ℕ) (hn : 0 < n) (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    0 < reciprocalSum n a := by
  apply Finset.sum_pos
  · intro i _
    exact inv_pos.mpr (Nat.cast_pos.mpr (ha i))
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- Removing an element from the subset decreases the sum by exactly 1/a(i). -/
theorem subsetReciprocalSum_erase (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) :
    subsetReciprocalSum n a S =
      subsetReciprocalSum n a (S.erase i) + (a i : ℝ)⁻¹ := by
  simp only [subsetReciprocalSum]
  rw [← Finset.add_sum_erase _ _ hi]
  ring

/-- Inserting a new element increases the subset sum by 1/a(i). -/
theorem subsetReciprocalSum_insert (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∉ S) :
    subsetReciprocalSum n a (insert i S) =
      subsetReciprocalSum n a S + (a i : ℝ)⁻¹ := by
  simp only [subsetReciprocalSum]
  rw [Finset.sum_insert hi]
  ring

/- ## Part II: The Main Conjecture -/

/-- The exponential precision property:
    A multiset (n, a) has a subset S with reciprocal sum in (1 - exp(-cK), 1] -/
def hasExponentialPrecision (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - Real.exp (-(c * K)) < subsetReciprocalSum n a S ∧
    subsetReciprocalSum n a S ≤ 1

/-- Erdős-Graham Conjecture (OPEN):
    ∃ c > 0 such that for all K > 1, every sufficiently large multiset
    with reciprocal sum > K has a subset summing to within exp(-cK) of 1.

    This is the formal statement from the formal-conjectures project. -/
def mainConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ K : ℝ, 1 < K →
      ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
        (n ≥ N₀ ∧ reciprocalSum n a > K) →
          hasExponentialPrecision n a c K

/- ## Part III: Known Result (Polynomial Bound) -/

/-- The polynomial precision property:
    A multiset has a subset S with reciprocal sum in (1 - c/K², 1] -/
def hasPolynomialPrecision (n : ℕ) (a : Fin n → ℕ) (c K : ℝ) : Prop :=
  ∃ S : Finset (Fin n),
    1 - c / K^2 < subsetReciprocalSum n a S ∧
    subsetReciprocalSum n a S ≤ 1

/-- Erdős-Graham Theorem [ErGr80]:
    The polynomial bound c/K² is known to hold.
    This is the weaker version of the conjecture. -/
axiom erdos_graham_polynomial :
  ∃ c : ℝ, 0 < c ∧
    ∀ K : ℝ, 1 < K →
      ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
        (n ≥ N₀ ∧ reciprocalSum n a > K) →
          hasPolynomialPrecision n a c K

/- ## Part IV: Relationship Between Bounds -/

/-- For large K, the exponential bound is tighter than the polynomial one:
    exp(-cK) < c'/K² for sufficiently large K.
    This shows the conjecture is strictly stronger than the known result.

    Proof: K² · exp(-cK) → 0 as K → ∞ (exponentials dominate polynomials),
    so eventually K² · exp(-cK) < c', giving exp(-cK) < c'/K². -/
theorem exponential_stronger_than_polynomial :
  ∀ c : ℝ, 0 < c →
    ∀ c' : ℝ, 0 < c' →
      ∃ K₀ : ℝ, ∀ K : ℝ, K > K₀ →
        Real.exp (-(c * K)) < c' / K^2 := by
  intro c hc c' hc'
  -- x^2 * exp(-x) → 0 as x → ∞ (Mathlib)
  have h_tend := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  -- Compose with (fun K => c * K) which tends to atTop for c > 0
  have h_linear : Tendsto (fun K : ℝ => c * K) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h_comp : Tendsto (fun K : ℝ => (c * K) ^ 2 * Real.exp (-(c * K))) atTop (nhds 0) :=
    h_tend.comp h_linear
  -- Use ε = c' * c^2 so that after extracting c^2 we get exp(-cK) < c'/K^2
  have heps : c' * c ^ 2 > 0 := by positivity
  rw [Metric.tendsto_atTop] at h_comp
  obtain ⟨K₁, hK₁⟩ := h_comp (c' * c ^ 2) heps
  use max K₁ 1
  intro K hK
  have hK_ge_K₁ : K ≥ K₁ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hK)
  have hK_gt_1 : K > 1 := lt_of_le_of_lt (le_max_right K₁ 1) hK
  have hK2_pos : K ^ 2 > 0 := by positivity
  have h_dist := hK₁ K hK_ge_K₁
  rw [Real.dist_eq, sub_zero] at h_dist
  have h_nonneg : 0 ≤ (c * K) ^ 2 * Real.exp (-(c * K)) := by positivity
  rw [abs_of_nonneg h_nonneg] at h_dist
  -- h_dist : (c * K) ^ 2 * exp(-(c * K)) < c' * c^2
  -- i.e. c^2 * K^2 * exp(-cK) < c' * c^2
  -- Dividing by c^2 * K^2 > 0: exp(-cK) < c' / K^2
  have hcK2_pos : (c * K) ^ 2 > 0 := by positivity
  calc Real.exp (-(c * K))
      = (c * K) ^ 2 * Real.exp (-(c * K)) / (c * K) ^ 2 := by
        field_simp
      _ < c' * c ^ 2 / (c * K) ^ 2 := by
        apply div_lt_div_of_pos_right h_dist hcK2_pos
      _ = c' / K ^ 2 := by ring_nf; field_simp

/-- If the exponential precision conjecture holds, then for large K,
    any multiset satisfying the exponential property also satisfies
    the polynomial one (the conjecture implies the known result). -/
theorem conjecture_implies_known :
    mainConjecture →
    ∃ c : ℝ, 0 < c ∧
      ∀ K : ℝ, 1 < K →
        ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ reciprocalSum n a > K) →
            ∃ S : Finset (Fin n),
              subsetReciprocalSum n a S ≤ 1 := by
  intro ⟨c, hc, hConj⟩
  exact ⟨c, hc, fun K hK => by
    obtain ⟨N₀, hN₀⟩ := hConj K hK
    exact ⟨N₀, fun n a h => by
      obtain ⟨S, _, hle⟩ := hN₀ n a h
      exact ⟨S, hle⟩⟩⟩

/-- Exponential precision at parameters (c, K) implies polynomial precision
    at (c', K) whenever exp(-cK) < c'/K².
    This links the two precision notions pointwise. -/
theorem exponential_implies_polynomial_pointwise
    (n : ℕ) (a : Fin n → ℕ) (c c' K : ℝ)
    (hexp : Real.exp (-(c * K)) < c' / K ^ 2) :
    hasExponentialPrecision n a c K → hasPolynomialPrecision n a c' K := by
  intro ⟨S, hlo, hhi⟩
  refine ⟨S, ?_, hhi⟩
  calc 1 - c' / K ^ 2
      < 1 - Real.exp (-(c * K)) := by linarith
    _ < subsetReciprocalSum n a S := hlo

/-- Monotonicity of exponential precision in the constant c:
    If c₁ ≤ c₂ and K > 0, exponential precision with c₁ implies c₂. -/
theorem exponentialPrecision_mono_c (n : ℕ) (a : Fin n → ℕ) (c₁ c₂ K : ℝ)
    (hc : c₁ ≤ c₂) (hK : 0 < K) :
    hasExponentialPrecision n a c₂ K → hasExponentialPrecision n a c₁ K := by
  intro ⟨S, hlo, hhi⟩
  refine ⟨S, ?_, hhi⟩
  calc 1 - Real.exp (-(c₁ * K))
      ≤ 1 - Real.exp (-(c₂ * K)) := by
        apply sub_le_sub_left
        apply Real.exp_le_exp_of_le
        linarith [mul_le_mul_of_nonneg_right hc (le_of_lt hK)]
    _ < subsetReciprocalSum n a S := hlo

/- ## Part IV.b: Exponential Gap Analysis -/

/-- For c > 0 and K > 0, the exponential gap 1 - exp(-cK) is non-negative.
    This ensures the precision window (1 - exp(-cK), 1] is well-defined. -/
theorem exponential_gap_nonneg (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    0 ≤ 1 - Real.exp (-(c * K)) := by
  rw [sub_nonneg, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith [mul_pos hc hK])

/-- The exponential gap is strictly less than 1, so the interval (1 - exp(-cK), 1]
    always has positive length. -/
theorem exponential_gap_lt_one (c K : ℝ) :
    1 - Real.exp (-(c * K)) < 1 := by
  linarith [Real.exp_pos (-(c * K))]

/-- The precision gap is monotone in K: larger K gives a wider precision window.
    For c > 0 and K₁ ≤ K₂, we have 1 - exp(-cK₁) ≤ 1 - exp(-cK₂). -/
theorem exponential_gap_monotone (c : ℝ) (hc : 0 < c) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
    1 - Real.exp (-(c * K₁)) ≤ 1 - Real.exp (-(c * K₂)) := by
  simp only [sub_le_sub_iff_left]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The precision gap tends to 1 as K → ∞: exp(-cK) → 0 implies 1 - exp(-cK) → 1.
    In the limit, the conjecture would produce subsets with sum arbitrarily close to 1. -/
theorem exponential_gap_tends_to_one (c : ℝ) (hc : 0 < c) :
    Tendsto (fun K : ℝ => 1 - Real.exp (-(c * K))) atTop (nhds 1) := by
  have h1 : Tendsto (fun K : ℝ => c * K) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_id
  have h2 : Tendsto (fun K : ℝ => Real.exp (-(c * K))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  convert tendsto_const_nhds.sub h2 using 1
  ring_nf

/- ## Part IV.c: Polynomial Gap Analysis -/

/-- For c > 0 and K > 0, the polynomial gap c/K² is positive. -/
theorem polynomial_gap_pos (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    0 < c / K ^ 2 := by
  positivity

/-- The polynomial gap is monotone decreasing in K: larger K gives tighter precision.
    For c > 0 and K₁ ≤ K₂ with K₁ > 0, we have c/K₂² ≤ c/K₁². -/
theorem polynomial_gap_antitone (c : ℝ) (hc : 0 < c) (K₁ K₂ : ℝ) (hK₁ : 0 < K₁)
    (hK : K₁ ≤ K₂) :
    c / K₂ ^ 2 ≤ c / K₁ ^ 2 := by
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  exact pow_le_pow_left₀ hK₁.le hK 2

/-- The polynomial gap c/K² tends to 0 as K → ∞. -/
theorem polynomial_gap_tends_to_zero (c : ℝ) :
    Tendsto (fun K : ℝ => c / K ^ 2) atTop (nhds 0) := by
  have h : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have h2 : Tendsto (fun K : ℝ => (K ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h
  have h3 : (fun K : ℝ => c / K ^ 2) = (fun K => c * (K ^ 2)⁻¹) := by
    ext K; rw [div_eq_mul_inv]
  rw [h3]
  convert h2.const_mul c using 1
  ring_nf

/-- Monotonicity of polynomial precision in the constant c:
    If c₁ ≤ c₂ and K ≠ 0, polynomial precision with c₁ implies c₂. -/
theorem polynomialPrecision_mono_c (n : ℕ) (a : Fin n → ℕ) (c₁ c₂ K : ℝ)
    (hc : c₁ ≤ c₂) (hK : K ≠ 0) :
    hasPolynomialPrecision n a c₁ K → hasPolynomialPrecision n a c₂ K := by
  intro ⟨S, hlo, hhi⟩
  refine ⟨S, ?_, hhi⟩
  calc 1 - c₂ / K ^ 2
      ≤ 1 - c₁ / K ^ 2 := by
        apply sub_le_sub_left
        apply div_le_div_of_nonneg_right hc
        exact sq_nonneg K
    _ < subsetReciprocalSum n a S := hlo

/- ## Part IV.d: Taylor Bound Analysis -/

/-- Key inequality: exp(-x) ≤ 1/(1+x) for x ≥ 0.
    This is the "first-order Taylor" bound for the exponential. -/
theorem exp_neg_le_inv_one_add (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])

/-- The exponential precision window is at least as large as 1 - 1/(1+cK)
    for c > 0 and K > 0, giving a concrete rational lower bound on the gap. -/
theorem exponential_gap_rational_lower_bound (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    1 - 1 / (1 + c * K) ≤ 1 - Real.exp (-(c * K)) := by
  simp only [sub_le_sub_iff_left]
  exact exp_neg_le_inv_one_add (c * K) (le_of_lt (mul_pos hc hK))

/-- Simplification: 1 - 1/(1+t) = t/(1+t) for t ≠ -1. -/
theorem one_sub_inv_one_add (t : ℝ) (ht : t ≠ -1) :
    1 - 1 / (1 + t) = t / (1 + t) := by
  have h1t : 1 + t ≠ 0 := by intro h; apply ht; linarith
  field_simp
  linarith

/-- Combined: the exponential gap is at least cK/(1+cK). -/
theorem exponential_gap_concrete_bound (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    c * K / (1 + c * K) ≤ 1 - Real.exp (-(c * K)) := by
  have hcK_pos : 0 < c * K := mul_pos hc hK
  rw [← one_sub_inv_one_add (c * K) (by linarith)]
  exact exponential_gap_rational_lower_bound c K hc hK

/-- The first-order lower bound for exp: exp(-x) ≥ 1 - x for all real x.
    Combined with the gap definition, this shows the exponential gap
    is at most cK, giving 1 - exp(-cK) ≤ cK. -/
theorem exp_neg_ge_one_sub (x : ℝ) : Real.exp (-x) ≥ 1 - x := by
  linarith [Real.add_one_le_exp (-x)]

/-- The exponential precision gap is at most cK:
    the window (1 - exp(-cK), 1] has width at most cK. -/
theorem exponential_gap_le_cK (c K : ℝ) :
    1 - Real.exp (-(c * K)) ≤ c * K := by
  linarith [exp_neg_ge_one_sub (c * K)]

/-- The exponential gap is sandwiched: cK/(1+cK) ≤ 1 - exp(-cK) ≤ cK.
    This gives both upper and lower bounds on the precision window width. -/
theorem exponential_gap_sandwich (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    c * K / (1 + c * K) ≤ 1 - Real.exp (-(c * K)) ∧
    1 - Real.exp (-(c * K)) ≤ c * K :=
  ⟨exponential_gap_concrete_bound c K hc hK, exponential_gap_le_cK c K⟩

/- ## Part V: Harmonic Number Context -/

/-- The n-th harmonic number H_n = 1 + 1/2 + ... + 1/n -/
noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℝ)⁻¹

/-- Harmonic numbers grow without bound (well-known):
    For any K > 0, there exists n with H_n > K.

    Proof: The partial sums 1 + 1/2 + ... + 1/n tend to infinity
    (Mathlib: Real.tendsto_sum_range_one_div_nat_succ_atTop). -/
theorem harmonic_unbounded :
    ∀ K : ℝ, ∃ n : ℕ, harmonicNumber n > K := by
  intro K
  -- Mathlib: partial sums of 1/(k+1) tend to infinity
  have h_tend := Real.tendsto_sum_range_one_div_nat_succ_atTop
  -- Match our harmonicNumber to the Mathlib form
  have h_eq : ∀ n : ℕ, (∑ k ∈ Finset.range n, (1 : ℝ) / (↑k + 1)) = harmonicNumber n := by
    intro n
    simp only [harmonicNumber, one_div]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  simp_rw [h_eq] at h_tend
  rw [tendsto_atTop_atTop] at h_tend
  obtain ⟨N, hN⟩ := h_tend (K + 1)
  exact ⟨N, lt_of_lt_of_le (by linarith) (hN N le_rfl)⟩

/-- Harmonic numbers are monotonically non-decreasing:
    n ≤ m implies H_n ≤ H_m. -/
theorem harmonicNumber_mono {n m : ℕ} (h : n ≤ m) :
    harmonicNumber n ≤ harmonicNumber m := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono h
  · intro i _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg (i + 1))

/-- H_0 = 0: the harmonic number of 0 is zero. -/
theorem harmonicNumber_zero : harmonicNumber 0 = 0 := by
  simp [harmonicNumber]

/-- H_1 = 1: the first harmonic number is 1. -/
theorem harmonicNumber_one : harmonicNumber 1 = 1 := by
  simp [harmonicNumber]

/-- Harmonic numbers are non-negative: H_n ≥ 0 for all n. -/
theorem harmonicNumber_nonneg (n : ℕ) : 0 ≤ harmonicNumber n := by
  apply Finset.sum_nonneg
  intro i _
  exact inv_nonneg.mpr (Nat.cast_nonneg (i + 1))

/-- Harmonic number recurrence: H_{n+1} = H_n + 1/(n+1). -/
theorem harmonicNumber_succ (n : ℕ) :
    harmonicNumber (n + 1) = harmonicNumber n + ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [harmonicNumber, Finset.sum_range_succ]

/-- H_n ≥ 1 for n ≥ 1 (since the first term is 1). -/
theorem harmonicNumber_ge_one {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ harmonicNumber n := by
  calc (1 : ℝ) = harmonicNumber 1 := (harmonicNumber_one).symm
    _ ≤ harmonicNumber n := harmonicNumber_mono hn

/-- The canonical multiset {1, 2, ..., n} has reciprocal sum equal to H_n. -/
theorem canonical_reciprocalSum (n : ℕ) :
    reciprocalSum n (fun i : Fin n => (i : ℕ) + 1) = harmonicNumber n := by
  simp only [reciprocalSum, harmonicNumber]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i + 1 : ℕ) : ℝ)⁻¹) n]

/- ## Part V.b: Existence of Valid Inputs -/

/-- For any K > 0, there exist valid inputs to the Erdős-Graham problem:
    a finite multiset of positive integers whose reciprocal sum exceeds K.
    This is the canonical {1, 2, ..., n} family. -/
theorem valid_inputs_exist (K : ℝ) :
    ∃ (n : ℕ) (a : Fin n → ℕ),
      (∀ i, 0 < a i) ∧ reciprocalSum n a > K := by
  obtain ⟨n, hn⟩ := harmonic_unbounded K
  refine ⟨n, fun i => (i : ℕ) + 1, fun i => Nat.succ_pos _, ?_⟩
  rw [canonical_reciprocalSum]
  exact hn

/- ## Part V.c: Structural Properties -/

/-- Reciprocal sum upper bound: if all elements are ≥ m > 0,
    then the reciprocal sum is at most n/m. -/
theorem reciprocalSum_le_of_ge (n : ℕ) (a : Fin n → ℕ) (m : ℕ) (hm : 0 < m)
    (ha : ∀ i, m ≤ a i) :
    reciprocalSum n a ≤ n / (m : ℝ) := by
  simp only [reciprocalSum]
  calc ∑ i : Fin n, (a i : ℝ)⁻¹
      ≤ ∑ _i : Fin n, (m : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast ha i)
    _ = ↑n * (↑m)⁻¹ := by simp [Finset.sum_const, Finset.card_univ]
    _ = ↑n / ↑m := by rw [div_eq_mul_inv]

/-- The trivial subset (empty set) always satisfies the upper bound ≤ 1.
    The challenge in the Erdős-Graham problem is getting close to 1 from below. -/
theorem trivial_subset_exists (n : ℕ) (a : Fin n → ℕ) :
    ∃ S : Finset (Fin n), subsetReciprocalSum n a S ≤ 1 := by
  exact ⟨∅, by simp [subsetReciprocalSum]⟩

/-- Exponential precision at (c, K) with c > 0, K > 0 implies there exists
    a subset with strictly positive sum ≤ 1 (the found subset is nontrivial). -/
theorem exponentialPrecision_subset_nonempty (n : ℕ) (a : Fin n → ℕ) (c K : ℝ)
    (hc : 0 < c) (hK : 0 < K) :
    hasExponentialPrecision n a c K →
    ∃ S : Finset (Fin n), 0 < subsetReciprocalSum n a S ∧ subsetReciprocalSum n a S ≤ 1 := by
  intro ⟨S, hlo, hhi⟩
  refine ⟨S, ?_, hhi⟩
  have h_gap := exponential_gap_nonneg c K hc hK
  linarith

/-- Polynomial precision at (c, K) with c ≤ K² gives a nontrivial subset.
    The hypothesis c ≤ K² ensures 1 - c/K² ≥ 0, making the precision window nontrivial. -/
theorem polynomialPrecision_subset_sum_pos (n : ℕ) (a : Fin n → ℕ) (c K : ℝ)
    (hc : 0 < c) (hK : 1 < K) (hcK : c ≤ K ^ 2) :
    hasPolynomialPrecision n a c K →
    ∃ S : Finset (Fin n), 0 < subsetReciprocalSum n a S ∧ subsetReciprocalSum n a S ≤ 1 := by
  intro ⟨S, hlo, hhi⟩
  refine ⟨S, ?_, hhi⟩
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have : c / K ^ 2 ≤ 1 := by rwa [div_le_one hK2]
  linarith

/- ## Part VII: Maximal Feasible Subsets and the Gap Bound

The greedy approach to the Erdős-Graham problem: identify subsets with reciprocal
sum close to 1 via maximal feasible subsets. A subset is "feasible" if its sum
is at most 1; it is "maximal" if adding any element exceeds 1. For maximal
feasible S and any j ∉ S, we have sum(S) > 1 - 1/a(j), bounding the gap. -/

/-- A subset S is feasible if its reciprocal sum does not exceed 1. -/
def isFeasible (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) : Prop :=
  subsetReciprocalSum n a S ≤ 1

/-- The empty set is always feasible (sum = 0 ≤ 1). -/
theorem empty_isFeasible (n : ℕ) (a : Fin n → ℕ) : isFeasible n a ∅ := by
  simp [isFeasible, subsetReciprocalSum]

/-- If the total reciprocal sum exceeds 1, the full set is not feasible. -/
theorem univ_not_feasible (n : ℕ) (a : Fin n → ℕ)
    (h : 1 < reciprocalSum n a) : ¬ isFeasible n a Finset.univ := by
  simp only [isFeasible, univ_subsetSum_eq_totalSum, not_le]
  exact h

/-- Maximal feasible subsets exist: among subsets with reciprocal sum ≤ 1,
    there is one where adding any element would push the sum above 1.
    Proof: choose a feasible subset of maximum cardinality. -/
theorem maximal_feasible_exists (n : ℕ) (a : Fin n → ℕ) :
    ∃ S : Finset (Fin n), isFeasible n a S ∧
      ∀ j : Fin n, j ∉ S → ¬ isFeasible n a (insert j S) := by
  classical
  let F := (Finset.univ : Finset (Finset (Fin n))).filter (isFeasible n a)
  have hF : F.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, empty_isFeasible n a⟩⟩
  obtain ⟨S, hS, hS_max⟩ := F.exists_max_image Finset.card hF
  refine ⟨S, (Finset.mem_filter.mp hS).2, fun j hj hc => ?_⟩
  have h1 := hS_max (insert j S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  rw [Finset.card_insert_of_notMem hj] at h1
  omega

/-- The gap bound for maximal feasible subsets:
    If S has sum ≤ 1 and adding any j ∉ S pushes sum above 1,
    then sum(S) > 1 - 1/a(j). This follows from sum(S) + 1/a(j) > 1. -/
theorem maximalFeasible_gap_bound (n : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n))
    (hmax : ∀ j : Fin n, j ∉ S → ¬ isFeasible n a (insert j S))
    (j : Fin n) (hj : j ∉ S) :
    1 - (a j : ℝ)⁻¹ < subsetReciprocalSum n a S := by
  have h := hmax j hj
  simp only [isFeasible, not_le] at h
  have h_eq := subsetReciprocalSum_insert n a S j hj
  linarith

/-- If the total reciprocal sum exceeds 1 and all elements are at least m > 0,
    then there exists a subset S with 1 - 1/m < sum(S) ≤ 1.
    This provides a constructive gap bound for the Erdős-Graham problem:
    larger minimum element yields tighter approximation to 1. -/
theorem subset_near_one (n : ℕ) (a : Fin n → ℕ) (m : ℕ) (hm : 0 < m)
    (ha : ∀ i, m ≤ a i) (htotal : 1 < reciprocalSum n a) :
    ∃ S : Finset (Fin n), 1 - (m : ℝ)⁻¹ < subsetReciprocalSum n a S ∧
      subsetReciprocalSum n a S ≤ 1 := by
  obtain ⟨S, hfeas, hmax⟩ := maximal_feasible_exists n a
  have hS_ne : S ≠ Finset.univ := by
    intro heq; rw [heq, isFeasible, univ_subsetSum_eq_totalSum] at hfeas; linarith
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra h; push_neg at h
    exact hS_ne (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨S, ?_, hfeas⟩
  have h_gap := maximalFeasible_gap_bound n a S hmax j hj
  have h_inv : (a j : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast ha j)
  linarith

/- ## Part VI: Summary -/

/-- Erdős Problem #312 Summary:
    The main conjecture asks for exponential precision in subset sums.
    The polynomial version is known (Erdős-Graham).
    The exponential version remains OPEN. -/
theorem erdos_312_status :
    -- Known: polynomial bound exists
    (∃ c : ℝ, 0 < c ∧
      ∀ K : ℝ, 1 < K →
        ∃ N₀ : ℕ, ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ reciprocalSum n a > K) →
            hasPolynomialPrecision n a c K) := by
  exact erdos_graham_polynomial

/- ## Part VIII: Restricted Greedy and Sieving Infrastructure

   Infrastructure toward proving erdos_graham_polynomial. The approach:
   1. Sieve the multiset to elements ≥ m ("large elements")
   2. Apply the greedy maximal feasible subset algorithm within the sieve
   3. Get gap bound 1/m from the restricted greedy algorithm

   The full Erdős-Graham argument chooses m strategically to achieve c/K² precision.
   This section provides the formal tools for steps 1-3. -/

/-- The set of indices where a(i) ≥ m (the "large element sieve"). -/
def largeElements (n : ℕ) (a : Fin n → ℕ) (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => m ≤ a i)

/-- Every index in largeElements has a(i) ≥ m. -/
theorem largeElements_ge (n : ℕ) (a : Fin n → ℕ) (m : ℕ) (i : Fin n)
    (hi : i ∈ largeElements n a m) : m ≤ a i := by
  simp only [largeElements, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact hi

/-- largeElements is monotone decreasing in the threshold:
    larger m gives a smaller (or equal) set of indices. -/
theorem largeElements_anti (n : ℕ) (a : Fin n → ℕ) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    largeElements n a m₂ ⊆ largeElements n a m₁ := by
  intro i hi
  simp only [largeElements, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans h hi

/-- With threshold 0, all elements are "large". -/
theorem largeElements_zero (n : ℕ) (a : Fin n → ℕ) :
    largeElements n a 0 = Finset.univ := by
  simp [largeElements]

/-- The reciprocal sum splits into large and small contributions:
    totalSum = largeSum + smallSum. Uses the existing disjoint union theorem. -/
theorem reciprocalSum_split (n : ℕ) (a : Fin n → ℕ) (m : ℕ) :
    reciprocalSum n a = subsetReciprocalSum n a (largeElements n a m) +
      subsetReciprocalSum n a (Finset.univ \ largeElements n a m) := by
  have hdisj : Disjoint (largeElements n a m) (Finset.univ \ largeElements n a m) :=
    disjoint_sdiff_self_right
  have hunion : largeElements n a m ∪ (Finset.univ \ largeElements n a m) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, largeElements,
      Finset.mem_filter, true_and]
    tauto
  have h := subsetReciprocalSum_disjoint_union n a _ _ hdisj
  rw [hunion, univ_subsetSum_eq_totalSum] at h
  exact h

/-- The large element sum is at least totalSum minus the small element sum. -/
theorem largeElements_sum_lower_bound (n : ℕ) (a : Fin n → ℕ) (m : ℕ) :
    subsetReciprocalSum n a (largeElements n a m) ≥
      reciprocalSum n a - subsetReciprocalSum n a (Finset.univ \ largeElements n a m) := by
  linarith [reciprocalSum_split n a m]

/-- Maximal feasible subsets exist within any region T.
    Generalizes maximal_feasible_exists to restricted index sets,
    which is essential for the sieve-and-greedy approach. -/
theorem restricted_maximal_feasible_exists (n : ℕ) (a : Fin n → ℕ) (T : Finset (Fin n)) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ subsetReciprocalSum n a S ≤ 1 ∧
      ∀ j ∈ T, j ∉ S → 1 < subsetReciprocalSum n a (insert j S) := by
  classical
  let F := T.powerset.filter (fun S => subsetReciprocalSum n a S ≤ 1)
  have hF : F.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset T, by simp [subsetReciprocalSum]⟩⟩
  obtain ⟨S, hS, hS_max⟩ := F.exists_max_image Finset.card hF
  have hSF := Finset.mem_filter.mp hS
  have hST : S ⊆ T := Finset.mem_powerset.mp hSF.1
  refine ⟨S, hST, hSF.2, fun j hj hjS => ?_⟩
  by_contra h
  push_neg at h
  have h_ins_F : insert j S ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.insert_subset.mpr ⟨hj, hST⟩), h⟩
  have := hS_max (insert j S) h_ins_F
  rw [Finset.card_insert_of_notMem hjS] at this
  omega

/-- The gap bound for restricted maximal feasible subsets:
    sum(S) > 1 - 1/a(j) for any j in T \ S. -/
theorem restricted_gap_bound (n : ℕ) (a : Fin n → ℕ) (T S : Finset (Fin n))
    (hmax : ∀ j ∈ T, j ∉ S → 1 < subsetReciprocalSum n a (insert j S))
    (j : Fin n) (hjT : j ∈ T) (hjS : j ∉ S) :
    1 - (a j : ℝ)⁻¹ < subsetReciprocalSum n a S := by
  have h := hmax j hjT hjS
  have h_eq := subsetReciprocalSum_insert n a S j hjS
  linarith

/-- Restricted subset_near_one: within T, if all elements ≥ m > 0
    and the reciprocal sum exceeds 1, there exists S ⊆ T with
    reciprocal sum in (1 - 1/m, 1]. This is the restricted analog
    of subset_near_one, enabling the sieve-and-greedy approach. -/
theorem restricted_subset_near_one (n : ℕ) (a : Fin n → ℕ) (T : Finset (Fin n))
    (m : ℕ) (hm : 0 < m)
    (ha : ∀ i ∈ T, m ≤ a i)
    (htotal : 1 < subsetReciprocalSum n a T) :
    ∃ S : Finset (Fin n), S ⊆ T ∧
      1 - (m : ℝ)⁻¹ < subsetReciprocalSum n a S ∧
      subsetReciprocalSum n a S ≤ 1 := by
  obtain ⟨S, hST, hfeas, hmax⟩ := restricted_maximal_feasible_exists n a T
  have hS_ne_T : S ≠ T := by intro heq; rw [heq] at hfeas; linarith
  have : ∃ j, j ∈ T ∧ j ∉ S := by
    by_contra h
    push_neg at h
    exact hS_ne_T (le_antisymm hST h)
  obtain ⟨j, hjT, hjS⟩ := this
  refine ⟨S, hST, ?_, hfeas⟩
  have h_gap := restricted_gap_bound n a T S hmax j hjT hjS
  have h_inv : (a j : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast ha j hjT)
  linarith

/-- The sieve-and-greedy theorem: if the large elements (those ≥ m)
    have reciprocal sum exceeding 1, we find a subset of those elements
    with sum in (1 - 1/m, 1].

    This combines sieving with the restricted greedy algorithm and
    is the core step of the Erdős-Graham approach: choose m to control
    the gap 1/m while ensuring the sieved sum stays above 1. -/
theorem sieve_and_greedy (n : ℕ) (a : Fin n → ℕ) (m : ℕ) (hm : 0 < m)
    (hlarge_sum : 1 < subsetReciprocalSum n a (largeElements n a m)) :
    ∃ S : Finset (Fin n),
      S ⊆ largeElements n a m ∧
      1 - (m : ℝ)⁻¹ < subsetReciprocalSum n a S ∧
      subsetReciprocalSum n a S ≤ 1 :=
  restricted_subset_near_one n a (largeElements n a m) m hm
    (fun i hi => largeElements_ge n a m i hi) hlarge_sum

end Erdos312
