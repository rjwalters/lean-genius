import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Proofs.AmgmInequalityOQ03

/-
# Power Mean Equality Condition: M_r = M_s iff All Elements Equal

## Open Question (cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01)

For positive weights w summing to 1 and positive reals z, the weighted power means satisfy:

  M_r(z, w) = M_t(z, w)  for 0 < r < t

**if and only if** all zᵢ are equal.

## What This Proves

**Main theorem**: `power_mean_eq_iff_all_eq_pos` — for 0 < r < t with strictly positive
weights summing to 1 and strictly positive reals, M_r = M_t iff all zᵢ are equal.
0 sorries, 0 axioms.

## Proof Strategy

Let A = Σ wᵢ zᵢʳ and B = Σ wᵢ zᵢᵗ. Both are positive.

**→ direction**: By contradiction. If some z_j ≠ z_k, then z_j^r ≠ z_k^r (rpow injectivity).
  By `StrictConvexOn.map_sum_lt` for f(x) = x^(t/r) (strictly convex since t/r > 1):
    A^(t/r) = f(Σ wᵢ zᵢʳ) < Σ wᵢ f(zᵢʳ) = Σ wᵢ (zᵢʳ)^(t/r) = Σ wᵢ zᵢᵗ = B.
  But M_r = M_t forces A^(t/r) = B (by raising both sides to t). Contradiction.

**← direction**: If all zᵢ = c then A = cʳ and B = cᵗ, giving M_r = c = M_t.

## Mathematical Context

Fills the equality case marked TODO in Mathlib's MeanInequalitiesPow.lean (line 36):
"each inequality A ≤ B should come with a theorem A = B ↔ _". Uses:
- `strictConvexOn_rpow` : x ↦ x^p strictly convex on [0,∞) for p > 1
- `StrictConvexOn.map_sum_lt` : strict Jensen inequality for finset sums
- `Real.rpow_left_inj` : injectivity of x ↦ x^p on nonneg reals for p ≠ 0
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace PowerMeanEqualityCase

open Real Finset

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

-- ============================================================
-- § 1: Supporting Lemmas
-- ============================================================

/-- Strictly positive weights summing to 1 implies the indexing set is nonempty. -/
lemma nonempty_of_pos_sum_one (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) : s.Nonempty := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · simp at hw'
  · exact h

/-- The weighted power sum ∑ wᵢ zᵢʳ is strictly positive when all weights and values are. -/
lemma power_sum_pos (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {r : ℝ} : 0 < ∑ i ∈ s, w i * z i ^ r := by
  apply sum_pos
  · intro i hi; exact mul_pos (hw i hi) (rpow_pos_of_pos (hz i hi) r)
  · exact nonempty_of_pos_sum_one s w hw hw'

-- ============================================================
-- § 2: Main Theorem
-- ============================================================

/-- **Power Mean Equality Condition** (positive exponents):

For 0 < r < t, strictly positive weights summing to 1, and strictly positive reals z,
  M_r(z, w) = M_t(z, w)  iff  all z_j = z_k for j, k ∈ s.

Equality characterization of `power_mean_monotone_pos` from AmgmInequalityOQ03.
Mathlib's MeanInequalitiesPow marks this case as a TODO (line 36-37). -/
theorem power_mean_eq_iff_all_eq_pos
    (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hrt : r < t) :
    weightedPowerMean s w z r (ne_of_gt hr) = weightedPowerMean s w z t (ne_of_gt ht) ↔
    ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  simp only [weightedPowerMean]
  set A := ∑ i ∈ s, w i * z i ^ r with hA_def
  set B := ∑ i ∈ s, w i * z i ^ t with hB_def
  have hA_pos : 0 < A := power_sum_pos s w z hw hw' hz
  have hB_pos : 0 < B := power_sum_pos s w z hw hw' hz
  have hA_nn : (0 : ℝ) ≤ A := le_of_lt hA_pos
  have hB_nn : (0 : ℝ) ≤ B := le_of_lt hB_pos
  have htr_gt1 : 1 < t / r := by
    have h_r_ne : r ≠ 0 := ne_of_gt hr
    have h_inv : 0 < r⁻¹ := inv_pos.mpr hr
    calc (1 : ℝ) = r * r⁻¹ := (mul_inv_cancel₀ h_r_ne).symm
      _ < t * r⁻¹ := mul_lt_mul_of_pos_right hrt h_inv
      _ = t / r := (div_eq_mul_inv t r).symm
  -- Membership in [0,∞) for zᵢʳ (needed for strict Jensen)
  have hmem : ∀ i ∈ s, z i ^ r ∈ Set.Ici (0 : ℝ) :=
    fun i hi => Set.mem_Ici.mpr (rpow_nonneg (le_of_lt (hz i hi)) r)
  -- Key identity: (zᵢʳ)^(t/r) = zᵢᵗ
  have h_pow_simp : ∀ i ∈ s, (z i ^ r) ^ (t / r) = z i ^ t := fun i hi => by
    rw [← rpow_mul (le_of_lt (hz i hi))]; congr 1; field_simp
  -- B expressed in terms of zᵢʳ
  have hB_rw : B = ∑ i ∈ s, w i * (z i ^ r) ^ (t / r) := by
    rw [hB_def]
    apply sum_congr rfl
    intro i hi; rw [← h_pow_simp i hi]
  constructor
  · -- → direction: M_r = M_t implies all zᵢ equal
    intro heq
    -- Step 1: M_r = M_t forces A^(t/r) = B
    have step1 : A ^ (t / r) = B := by
      have h1 : A ^ (t / r) = (A ^ (1 / r)) ^ t := by
        rw [← rpow_mul hA_nn]; congr 1; ring
      have h2 : (B ^ (1 / t)) ^ t = B := by
        rw [← rpow_mul hB_nn]
        have : (1 : ℝ) / t * t = 1 := by field_simp
        rw [this, rpow_one]
      calc A ^ (t / r) = (A ^ (1 / r)) ^ t := h1
        _ = (B ^ (1 / t)) ^ t := by rw [heq]
        _ = B := h2
    -- Step 2: If any zᵢ ≠ zⱼ, strict Jensen contradicts step1
    have h_all_zr : ∀ j ∈ s, ∀ k ∈ s, z j ^ r = z k ^ r := by
      by_contra h_not
      push_neg at h_not
      obtain ⟨j, hj, k, hk, hjkr⟩ := h_not
      -- Strict Jensen: f(A) < Σ wᵢ f(zᵢʳ) when inputs are non-constant
      have hlt : A ^ (t / r) < B := by
        have hsc := strictConvexOn_rpow htr_gt1
        have key := hsc.map_sum_lt (fun i hi => hw i hi) hw' hmem ⟨j, hj, k, hk, hjkr⟩
        calc A ^ (t / r)
            = (fun x : ℝ => x ^ (t / r)) (∑ i ∈ s, w i • z i ^ r) := by
              simp only [smul_eq_mul, ← hA_def]
          _ < ∑ i ∈ s, w i • (fun x : ℝ => x ^ (t / r)) (z i ^ r) := key
          _ = B := by
              simp only [smul_eq_mul]
              exact hB_rw.symm
      exact absurd step1 (ne_of_lt hlt)
    -- Step 3: z_jʳ = z_kʳ implies z_j = z_k (rpow injectivity)
    intro j hj k hk
    exact (rpow_left_inj (le_of_lt (hz j hj)) (le_of_lt (hz k hk))
        (ne_of_gt hr)).mp (h_all_zr j hj k hk)
  · -- ← direction: all equal implies M_r = M_t
    intro hall
    obtain ⟨i₀, hi₀⟩ := nonempty_of_pos_sum_one s w hw hw'
    have hc_pos : 0 < z i₀ := hz i₀ hi₀
    have hall' : ∀ i ∈ s, z i = z i₀ := fun i hi => hall i hi i₀ hi₀
    -- When all zᵢ = z i₀: A = z i₀ ^ r and B = z i₀ ^ t
    have hA_eq : A = z i₀ ^ r :=
      calc A = ∑ i ∈ s, w i * z i ^ r := hA_def
        _ = ∑ i ∈ s, w i * z i₀ ^ r := sum_congr rfl fun i hi => by rw [hall' i hi]
        _ = z i₀ ^ r := by rw [← sum_mul, hw', one_mul]
    have hB_eq : B = z i₀ ^ t :=
      calc B = ∑ i ∈ s, w i * z i ^ t := hB_def
        _ = ∑ i ∈ s, w i * z i₀ ^ t := sum_congr rfl fun i hi => by rw [hall' i hi]
        _ = z i₀ ^ t := by rw [← sum_mul, hw', one_mul]
    -- (z i₀ ^ r) ^ (1/r) = z i₀ and (z i₀ ^ t) ^ (1/t) = z i₀
    have h_lhs : A ^ (1 / r) = z i₀ := by
      rw [hA_eq, ← rpow_mul (le_of_lt hc_pos)]
      have : r * (1 / r) = 1 := by field_simp
      rw [this, rpow_one]
    have h_rhs : B ^ (1 / t) = z i₀ := by
      rw [hB_eq, ← rpow_mul (le_of_lt hc_pos)]
      have : t * (1 / t) = 1 := by field_simp
      rw [this, rpow_one]
    rw [h_lhs, h_rhs]

-- ============================================================
-- § 3: Corollaries
-- ============================================================

/-- **AM = QM iff all equal**: Arithmetic mean equals quadratic mean iff all zᵢ equal.
    Special case r = 1, t = 2. -/
theorem am_eq_qm_iff_all_eq
    (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z 1 one_ne_zero = weightedPowerMean s w z 2 two_ne_zero ↔
    ∀ j ∈ s, ∀ k ∈ s, z j = z k :=
  power_mean_eq_iff_all_eq_pos s w z hw hw' hz one_pos two_pos one_lt_two

/-- **Strict AM < QM when values differ**: If some z_j ≠ z_k, the arithmetic mean is
    strictly less than the quadratic mean. -/
theorem am_lt_qm_of_not_all_eq
    (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z 1 one_ne_zero < weightedPowerMean s w z 2 two_ne_zero := by
  apply lt_of_le_of_ne
  · exact power_mean_monotone_pos s w z (fun i hi => le_of_lt (hw i hi)) hw' hz
      one_pos one_le_two one_ne_zero two_ne_zero
  · intro h_eq
    have h_all := (am_eq_qm_iff_all_eq s w z hw hw' hz).mp h_eq
    obtain ⟨j, hj, k, hk, hjk⟩ := hne
    exact hjk (h_all j hj k hk)

end PowerMeanEqualityCase
