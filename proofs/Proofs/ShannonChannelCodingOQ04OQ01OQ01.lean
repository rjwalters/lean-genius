/-
  Shannon Channel Coding OQ-04-OQ-01-OQ-01: Unique Maximum of Binary Entropy

  Open Question (shannon-channel-coding-oq-04-oq-01):
  "Prove that the maximum of h(p) = log 2 is achieved uniquely at p = 1/2."

  Strategy: Use strict concavity of h (OQ-01). For p ∈ (0,1) with p ≠ 1/2:
  - Write 1/2 = (1/2)·p + (1/2)·(1-p) as the midpoint of p and (1-p)
  - Since h(1-p) = h(p) by symmetry and p ≠ 1-p (because p ≠ 1/2):
  - By strict concavity: h(1/2) > (1/2)·h(p) + (1/2)·h(1-p) = h(p)
  For boundary: h(0) = h(1) = 0 < log 2 (from parent).

  New results (not in parent proofs):
  - h_deriv_zero_iff: h'(p) = 0 iff p = 1/2 (unique critical point)
  - h_lt_h_half: h(p) < log 2 for p ∈ (0,1) with p ≠ 1/2 (strict bound)
  - h_eq_log_two_iff: h(p) = log 2 iff p = 1/2 on [0,1]
  - hBits_eq_one_iff: h₂(p) = 1 iff p = 1/2 on [0,1]
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ04
import Proofs.ShannonChannelCodingOQ04OQ01

namespace InformationTheory.BinaryEntropy

open Real Set

-- ============================================================
-- Section 1: Unique Critical Point
-- ============================================================

/-- The first derivative h'(p) = log(1-p) - log(p) vanishes iff p = 1/2.
    From the parent OQ-01, h'(p) is the derivative of h. A zero of h' means
    log(1-p) = log(p), hence 1-p = p (by injectivity of exp), hence p = 1/2. -/
theorem h_deriv_zero_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.log (1 - p) - Real.log p = 0 ↔ p = 1 / 2 := by
  constructor
  · intro hd
    have heq : Real.log (1 - p) = Real.log p := by linarith
    have h1p0 : (0 : ℝ) < 1 - p := by linarith
    have hab : 1 - p = p := by
      have := congr_arg Real.exp heq
      rwa [Real.exp_log h1p0, Real.exp_log hp0] at this
    linarith
  · rintro rfl
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, sub_self]

-- ============================================================
-- Section 2: Strict Maximum on (0,1)
-- ============================================================

/-- For p ∈ (0,1) with p ≠ 1/2, h(p) < h(1/2) = log 2.
    Core: by strict concavity of h (OQ-01), with the midpoint decomposition
    1/2 = (1/2)p + (1/2)(1-p) and symmetry h(1-p) = h(p). -/
theorem h_lt_h_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hne : p ≠ 1 / 2) :
    h p < h (1 / 2) := by
  have hp : p ∈ Ioo 0 1 := ⟨hp0, hp1⟩
  have h1mp : 1 - p ∈ Ioo 0 1 := ⟨by linarith, by linarith⟩
  have hpne : p ≠ 1 - p := by intro heq; exact hne (by linarith)
  -- Apply strict concavity with midpoint decomposition
  have hsc : (1 / 2 : ℝ) • h p + (1 / 2 : ℝ) • h (1 - p) <
      h ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • (1 - p)) :=
    h_strictConcaveOn.2 hp h1mp hpne (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hsc
  -- (1/2)*p + (1/2)*(1-p) = 1/2
  rw [show (1 / 2 : ℝ) * p + 1 / 2 * (1 - p) = 1 / 2 from by ring] at hsc
  -- h(1-p) = h(p) by symmetry
  rw [← h_symm p] at hsc
  linarith

-- ============================================================
-- Section 3: Unique Maximum Characterization
-- ============================================================

/-- The unique maximum of binary entropy on [0,1] is h(p) = log 2, achieved
    iff p = 1/2. This answers the open question from OQ-01.
    BSC interpretation: the binary symmetric channel BSC(p) has capacity
    1 - h₂(p), which is minimized uniquely at p = 1/2 (the useless channel). -/
theorem h_eq_log_two_iff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    h p = log 2 ↔ p = 1 / 2 := by
  constructor
  · intro heq
    by_contra hne
    by_cases h0 : p = 0
    · rw [h0, h_zero] at heq
      exact absurd heq (ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    by_cases h1 : p = 1
    · rw [h1, h_one] at heq
      exact absurd heq (ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    · have hp0' : (0 : ℝ) < p := lt_of_le_of_ne hp0 (Ne.symm h0)
      have hp1' : p < 1 := lt_of_le_of_ne hp1 h1
      linarith [h_lt_h_half hp0' hp1' hne, h_half.symm ▸ heq.symm.le]
  · rintro rfl; exact h_half

/-- Binary entropy in bits achieves 1 iff p = 1/2.
    Corollary: BSC capacity 1 - h₂(p) achieves 0 iff p = 1/2. -/
theorem hBits_eq_one_iff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hBits p = 1 ↔ p = 1 / 2 := by
  unfold hBits
  rw [div_eq_one_iff_eq (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  exact h_eq_log_two_iff hp0 hp1

end InformationTheory.BinaryEntropy
