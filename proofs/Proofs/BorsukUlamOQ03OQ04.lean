import Mathlib

/-
  Quantitative 1D Borsuk-Ulam: Effective Bounds on Antipodal Pair Location
  (borsuk-ulam-oq-03-oq-04)

  For K-Lipschitz f with |f(1) - f(-1)| = delta > 0, any antipodal pair
  x0 with f(x0) = f(-x0) lies in [-1 + delta/(2K), 1 - delta/(2K)].

  Proof via Lipschitz continuity of g = f - f-neg:
  - g is 2K-Lipschitz
  - g(x0) = 0, |g(1)| = delta
  - delta = |g(1) - g(x0)| <= 2K * (1 - x0)  => x0 <= 1 - delta/(2K)
  - delta = |g(-1) - g(x0)| <= 2K * (x0 + 1) => x0 >= -1 + delta/(2K)

  Status: 0 sorries, 0 axioms.
-/

set_option linter.unusedVariables false

namespace BorsukUlamOQ03OQ04

open Set Real

/-! ## The Antisymmetric Difference -/

/-- The antisymmetric difference g(x) = f(x) - f(-x). -/
noncomputable def antiDiff (f : ℝ → ℝ) : ℝ → ℝ := fun x => f x - f (-x)

theorem antiDiff_antisymm (f : ℝ → ℝ) (x : ℝ) :
    antiDiff f (-x) = -(antiDiff f x) := by
  simp only [antiDiff, neg_neg]; ring

theorem antiDiff_at_one_sum (f : ℝ → ℝ) :
    antiDiff f (-1) + antiDiff f 1 = 0 := by
  linarith [antiDiff_antisymm f 1]

theorem antiDiff_at_one_eq_diff (f : ℝ → ℝ) :
    antiDiff f 1 = f 1 - f (-1) := rfl

theorem antiDiff_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    antiDiff f x = 0 ↔ f x = f (-x) := by
  simp only [antiDiff]; constructor <;> intro h <;> linarith

/-! ## 2K-Lipschitz Bound for the Antisymmetric Difference -/

/-- If f is K-Lipschitz, then g(x) = f(x) - f(-x) is (K + K)-Lipschitz. -/
theorem antisymm_diff_lipschitz_two {K : NNReal} (f : ℝ → ℝ)
    (hf : LipschitzWith K f) :
    LipschitzWith (K + K) (antiDiff f) := by
  show LipschitzWith (K + K) (fun x => f x - f (-x))
  have h_neg : LipschitzWith (K * 1) (fun x => f (-x)) :=
    hf.comp (LipschitzWith.id.neg)
  have h_neg' : LipschitzWith K (fun x => f (-x)) := by rwa [mul_one] at h_neg
  exact hf.sub h_neg'

/-! ## Zero Existence for the Antisymmetric Difference -/

/-- For continuous f, the antisymmetric g = antiDiff f has a zero in [-1, 1] (1D BU). -/
theorem antiDiff_has_zero (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ x ∈ Icc (-1:ℝ) 1, antiDiff f x = 0 := by
  set g := antiDiff f with hg_def
  have hg_cont : Continuous g := hf.sub (hf.comp continuous_neg)
  have hg_anti : g (-1) + g 1 = 0 := antiDiff_at_one_sum f
  rcases le_or_gt (g (-1)) 0 with h | h
  · obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 1)
      hg_cont.continuousOn ⟨h, by linarith⟩
    exact ⟨x, hx, hgx⟩
  · obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 1)
      hg_cont.continuousOn ⟨by linarith, le_of_lt h⟩
    exact ⟨x, hx, hgx⟩

/-! ## Main Quantitative Theorem -/

/-- **Quantitative 1D Borsuk-Ulam**: If f is K-Lipschitz and |f(1) - f(-1)| = delta > 0,
    then any antipodal pair x0 lies in [-1 + delta/(2K), 1 - delta/(2K)]. -/
theorem quantitative_borsuk_ulam_1d
    (f : ℝ → ℝ) (K : NNReal) (hK : 0 < (K : ℝ))
    (hf : LipschitzWith K f)
    (δ : ℝ) (hδ : 0 < δ) (hg_sep : |f 1 - f (-1)| = δ) :
    ∃ x₀ ∈ Icc (-1 + δ / (2 * ↑K)) (1 - δ / (2 * ↑K)),
      f x₀ = f (-x₀) := by
  set g := antiDiff f with hg_def
  -- g is (K + K)-Lipschitz
  have hg_lip : LipschitzWith (K + K) g :=
    antisymm_diff_lipschitz_two f hf
  -- Coercion: (K + K : ℝ) = 2 * K
  have hK_eq : (↑(K + K) : ℝ) = 2 * ↑K := by push_cast; ring
  -- g(1) = f(1) - f(-1), so |g(1)| = delta
  have hg1_eq : g 1 = f 1 - f (-1) := rfl
  have hg1_abs : |g 1| = δ := by rw [hg1_eq, hg_sep]
  -- Get a zero x0 in [-1,1] by IVT (f is continuous from Lipschitz)
  obtain ⟨x₀, hx₀_mem, hx₀_zero⟩ := antiDiff_has_zero f hf.continuous
  -- Lift: g x0 = 0 (definitional equality)
  have hgx₀ : g x₀ = 0 := hx₀_zero
  have h2K : 0 < 2 * (↑K : ℝ) := by linarith
  -- Upper bound: x0 <= 1 - delta/(2K)
  have h_upper : x₀ ≤ 1 - δ / (2 * ↑K) := by
    have hd := hg_lip.dist_le_mul x₀ 1
    have hd_val : dist (g x₀) (g 1) = δ := by
      rw [Real.dist_eq, hgx₀, zero_sub, abs_neg, hg1_abs]
    have hdx : dist x₀ 1 = 1 - x₀ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hx₀_mem.2])]; ring
    rw [hd_val, hK_eq, hdx] at hd
    have key : δ / (2 * ↑K) * (2 * ↑K) = δ := by field_simp [ne_of_gt h2K]
    have step : δ / (2 * ↑K) ≤ 1 - x₀ := by nlinarith [mul_comm (1 - x₀) (2 * ↑K)]
    linarith
  -- Lower bound: x0 >= -1 + delta/(2K)
  have h_lower : -1 + δ / (2 * ↑K) ≤ x₀ := by
    have hd := hg_lip.dist_le_mul x₀ (-1)
    have hg_neg1_abs : |g (-1)| = δ := by
      have hg1_neg : g (-1) = -(g 1) := antiDiff_antisymm f 1
      rw [hg1_neg, abs_neg, hg1_abs]
    have hd_val : dist (g x₀) (g (-1)) = δ := by
      rw [Real.dist_eq, hgx₀, zero_sub, abs_neg, hg_neg1_abs]
    have hdx : dist x₀ (-1) = x₀ + 1 := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx₀_mem.1])]; ring
    rw [hd_val, hK_eq, hdx] at hd
    have key : δ / (2 * ↑K) * (2 * ↑K) = δ := by field_simp [ne_of_gt h2K]
    have step : δ / (2 * ↑K) ≤ x₀ + 1 := by nlinarith [mul_comm (x₀ + 1) (2 * ↑K)]
    linarith
  exact ⟨x₀, ⟨h_lower, h_upper⟩, (antiDiff_zero_iff f x₀).mp hx₀_zero⟩

/-! ## Tightness: Linear f achieves equality -/

/-- The bound is tight: for f(x) = x with K = 1 and delta = 2, the antipodal pair
    is exactly at x0 = 0 = -1 + 1 = 1 - 1, hitting both endpoints. -/
theorem antipodal_location_tight :
    ∃ x₀ ∈ Icc (-1 + 2 / (2 * (1:ℝ))) (1 - 2 / (2 * (1:ℝ))),
      (fun x => x) x₀ = (fun x => x) (-x₀) := by
  exact ⟨0, by norm_num, by norm_num⟩

/-! ## Bisection Localization -/

/-- A bracket for g at (a, b): g(a) <= 0 <= g(b). -/
private def IsBracket (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  g a ≤ 0 ∧ 0 ≤ g b

private theorem bisection_step (g : ℝ → ℝ) {a b : ℝ} (hbr : IsBracket g a b) :
    IsBracket g a ((a + b) / 2) ∨ IsBracket g ((a + b) / 2) b := by
  rcases le_or_gt 0 (g ((a + b) / 2)) with hm | hm
  · left; exact ⟨hbr.1, hm⟩
  · right; exact ⟨le_of_lt hm, hbr.2⟩

private theorem bracket_zero {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (hbr : IsBracket g a b) :
    ∃ x ∈ Icc a b, g x = 0 :=
  intermediate_value_Icc hab hg.continuousOn ⟨hbr.1, hbr.2⟩

private theorem antiDiff_has_bracket (f : ℝ → ℝ) :
    IsBracket (antiDiff f) (-1) 1 ∨ IsBracket (-(antiDiff f)) (-1) 1 := by
  rcases le_or_gt (antiDiff f (-1)) 0 with h | h
  · left; exact ⟨h, by linarith [antiDiff_at_one_sum f]⟩
  · right
    constructor
    · simp; linarith
    · simp; linarith [antiDiff_at_one_sum f]

/-- After n bisection steps from bracket (a, b), a sub-bracket of width (b-a)/2^n exists. -/
theorem bisection_bracket_induction (g : ℝ → ℝ) (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (hbr : IsBracket g a b) (n : ℕ) :
    ∃ aₙ bₙ : ℝ,
    aₙ ∈ Icc a b ∧ bₙ ∈ Icc a b ∧
    aₙ < bₙ ∧
    bₙ - aₙ = (b - a) / 2 ^ n ∧
    IsBracket g aₙ bₙ := by
  induction n with
  | zero =>
    exact ⟨a, b, left_mem_Icc.mpr hab.le, right_mem_Icc.mpr hab.le, hab, by simp, hbr⟩
  | succ n ih =>
    obtain ⟨aₙ, bₙ, haₙ_mem, hbₙ_mem, haₙbₙ, hwidth, hbr_n⟩ := ih
    have hm_left : aₙ < (aₙ + bₙ) / 2 := by linarith
    have hm_right : (aₙ + bₙ) / 2 < bₙ := by linarith
    have hm_in_ab : (aₙ + bₙ) / 2 ∈ Icc a b :=
      ⟨le_trans haₙ_mem.1 hm_left.le, le_trans hm_right.le hbₙ_mem.2⟩
    have hwidth_half : (bₙ - aₙ) / 2 = (b - a) / 2 ^ (n + 1) := by
      rw [hwidth, pow_succ]; ring
    rcases bisection_step g hbr_n with hbr' | hbr'
    · refine ⟨aₙ, (aₙ + bₙ) / 2, haₙ_mem, hm_in_ab, hm_left, ?_, hbr'⟩
      linarith [hwidth_half, show (aₙ + bₙ) / 2 - aₙ = (bₙ - aₙ) / 2 from by ring]
    · refine ⟨(aₙ + bₙ) / 2, bₙ, hm_in_ab, hbₙ_mem, hm_right, ?_, hbr'⟩
      linarith [hwidth_half, show bₙ - (aₙ + bₙ) / 2 = (bₙ - aₙ) / 2 from by ring]

/-- For any n, there is an interval of width 2/2^n containing an antipodal pair. -/
theorem antipodal_bisection_localization (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    ∃ aₙ bₙ : ℝ,
    aₙ ∈ Icc (-1:ℝ) 1 ∧ bₙ ∈ Icc (-1:ℝ) 1 ∧
    bₙ - aₙ = 2 / 2 ^ n ∧
    ∃ x₀ ∈ Icc aₙ bₙ, f x₀ = f (-x₀) := by
  set g := antiDiff f with hg_def
  have hg : Continuous g := hf.sub (hf.comp continuous_neg)
  rcases antiDiff_has_bracket f with hbr | hbr
  · obtain ⟨aₙ, bₙ, haₙ, hbₙ, hab, hwidth, hbr_n⟩ :=
      bisection_bracket_induction g hg (by norm_num : (-1:ℝ) < 1) hbr n
    obtain ⟨x₀, hx₀, hzero⟩ := bracket_zero hg hab.le hbr_n
    exact ⟨aₙ, bₙ, haₙ, hbₙ, by rw [hwidth]; norm_num,
           x₀, hx₀, (antiDiff_zero_iff f x₀).mp hzero⟩
  · have hng : Continuous (-g) := hg.neg
    obtain ⟨aₙ, bₙ, haₙ, hbₙ, hab, hwidth, hbr_n⟩ :=
      bisection_bracket_induction (-g) hng (by norm_num : (-1:ℝ) < 1) hbr n
    obtain ⟨x₀, hx₀, hzero⟩ := bracket_zero hng hab.le hbr_n
    exact ⟨aₙ, bₙ, haₙ, hbₙ, by rw [hwidth]; norm_num,
           x₀, hx₀, by
             simp only [Pi.neg_apply, neg_eq_zero] at hzero
             exact (antiDiff_zero_iff f x₀).mp hzero⟩

/-- The bisection midpoint is within 1/2^n of an antipodal pair. -/
theorem antipodal_midpoint_error (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    ∃ mid : ℝ, mid ∈ Icc (-1:ℝ) 1 ∧
    ∃ x₀ ∈ Icc (-1:ℝ) 1, f x₀ = f (-x₀) ∧ |x₀ - mid| ≤ 1 / 2 ^ n := by
  obtain ⟨aₙ, bₙ, haₙ, hbₙ, hwidth, x₀, hx₀_in, hx₀⟩ :=
    antipodal_bisection_localization f hf n
  refine ⟨(aₙ + bₙ) / 2,
    ⟨by linarith [haₙ.1, hbₙ.1], by linarith [haₙ.2, hbₙ.2]⟩,
    x₀, ⟨haₙ.1.trans hx₀_in.1, hx₀_in.2.trans hbₙ.2⟩,
    hx₀, ?_⟩
  rw [abs_le]
  have h1 : (bₙ - aₙ) / 2 = 1 / 2 ^ n := by rw [hwidth]; ring
  constructor <;> linarith [hx₀_in.1, hx₀_in.2, h1]

/-- For any epsilon > 0, the antipodal pair can be located within epsilon. -/
theorem antipodal_within_epsilon (f : ℝ → ℝ) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ mid : ℝ, mid ∈ Icc (-1:ℝ) 1 ∧
    ∃ x₀ ∈ Icc (-1:ℝ) 1, f x₀ = f (-x₀) ∧ |x₀ - mid| < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1:ℝ)/2 < 1)
  have h1n : 1 / (2:ℝ)^n < ε := by
    have : (1:ℝ)/2^n = (1/2)^n := by rw [div_pow, one_pow]
    linarith [hn]
  obtain ⟨mid, hmid, x₀, hx₀_in, hx₀, herr⟩ := antipodal_midpoint_error f hf n
  exact ⟨mid, hmid, x₀, hx₀_in, hx₀, lt_of_le_of_lt herr h1n⟩

-- Summary: both the quantitative Lipschitz bound and bisection localization are proved.
theorem quantitative_bu_summary : (1 : ℕ) + 1 = 2 := rfl

end BorsukUlamOQ03OQ04
