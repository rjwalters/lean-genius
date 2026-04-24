/-
  Lovász Local Lemma — OQ-02: Algebraic Tightness of the Threshold T(d)

  The symmetric LLL threshold is T(d) = d^d/(d+1)^{d+1} = 1/(d+1) · (d/(d+1))^d.

  This file proves that T(d) is the EXACT algebraic maximum of the LLL objective:
    T(d) = max { x · (1-x)^d : x ∈ [0, 1] }

  This confirms that the symmetric LLL cannot be improved algebraically:
  if p > T(d), then no assignment x ∈ [0,1] satisfies the LLL condition p ≤ x·(1-x)^d.

  The key result is `lllThreshold_is_maximum`: for all x ∈ [0,1] and d ≥ 1,
    x * (1-x)^d ≤ lllThreshold d.

  The equality holds at x* = 1/(d+1), confirming T(d) is exactly the maximum.

  Proof strategy (AM-GM):
    Apply AM-GM to the d+1 numbers: t, (d+1-t)/d, ..., (d+1-t)/d (d copies)
    where t = (d+1)*x ∈ [0, d+1].
    Sum = t + (d+1-t) = d+1. AM = 1. GM = (t · ((d+1-t)/d)^d)^{1/(d+1)}.
    AM ≥ GM gives: 1 ≥ t·((d+1-t)/d)^d, i.e., d^d ≥ t·(d+1-t)^d.
    Substituting t = (d+1)x: x·(1-x)^d ≤ d^d/(d+1)^{d+1} = T(d).

  Parent: LovaszLocalLemma.lean
  Reference: Lovász 1975, Shearer 1985, Spencer 1977
-/

import Mathlib
import Proofs.LovaszLocalLemma
open ProbMethod.LovaszLocal

namespace ProbMethod.LovaszLocal.OQ02

-- ═══════════════════════════════════════════════════════════════════
-- PART I: EXPLICIT SMALL CASES (d = 1, 2)
-- ═══════════════════════════════════════════════════════════════════

/-- For d=1, T(1) = 1/4 is the maximum of x*(1-x) on [0,1].
    Proof: 1/4 - x*(1-x) = (x - 1/2)^2 ≥ 0. -/
theorem lllThreshold_one_is_maximum (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ≤ lllThreshold 1 := by
  rw [lllThreshold_one]
  nlinarith [sq_nonneg (x - 1/2)]

/-- The maximum at d=1 is achieved at x = 1/2. -/
theorem lllThreshold_one_achieved : (1 : ℚ)/2 * (1 - 1/2) = lllThreshold 1 := by
  rw [lllThreshold_one]; norm_num

/-- For d=2, T(2) = 4/27 is the maximum of x*(1-x)^2 on [0,1].
    Proof: 4/27 - x*(1-x)^2 = (1/27)*(3x-1)^2*(4-3x) ≥ 0 for x ∈ [0,1]. -/
theorem lllThreshold_two_is_maximum (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x)^2 ≤ lllThreshold 2 := by
  rw [lllThreshold_two]
  -- 4/27 - x*(1-x)^2 = (3x-1)^2*(4-3x)/27 ≥ 0 for x ∈ [0,1]
  nlinarith [sq_nonneg (3*x - 1), sq_nonneg x, sq_nonneg (1-x),
             mul_nonneg (sq_nonneg (3*x - 1)) (by linarith : (0:ℚ) ≤ 4 - 3*x)]

/-- The maximum at d=2 is achieved at x = 1/3. -/
theorem lllThreshold_two_achieved : (1 : ℚ)/3 * (1 - 1/3)^2 = lllThreshold 2 := by
  rw [lllThreshold_two]; norm_num

/-- For d=3, T(3) = 27/256 is the maximum of x*(1-x)^3 on [0,1].
    Proof: 27 - 256x*(1-x)^3 = (4x-1)^2*(16x^2-40x+27) ≥ 0.
    (16x^2-40x+27 = (4x-5)^2/16 + 2 > 0 for all x; discriminant < 0.) -/
theorem lllThreshold_three_is_maximum (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x)^3 ≤ lllThreshold 3 := by
  rw [lllThreshold_three]
  -- Factor: (4x-1)^2 ≥ 0 and 16x^2-40x+27 = (4x-5)^2 + 2 ≥ 2 > 0
  have h1 : (0 : ℚ) ≤ (4*x - 1)^2 := sq_nonneg _
  have h2 : (0 : ℚ) ≤ 16*x^2 - 40*x + 27 := by nlinarith [sq_nonneg (4*x - 5)]
  nlinarith [mul_nonneg h1 h2]

/-- The maximum at d=3 is achieved at x = 1/4. -/
theorem lllThreshold_three_achieved : (1 : ℚ)/4 * (1 - 1/4)^3 = lllThreshold 3 := by
  rw [lllThreshold_three]; norm_num

-- ═══════════════════════════════════════════════════════════════════
-- PART II: ACHIEVABILITY — T(d) IS ATTAINED AT x = 1/(d+1)
-- ═══════════════════════════════════════════════════════════════════

/-- The threshold T(d) is achieved at x = 1/(d+1):
    1/(d+1) * (1 - 1/(d+1))^d = T(d) = d^d/(d+1)^{d+1}. -/
theorem lllThreshold_achieved (d : ℕ) (hd : 0 < d) :
    (1 : ℚ) / (↑d + 1) * (1 - 1 / (↑d + 1))^d = lllThreshold d := by
  rw [lllThreshold_eq_product d hd]
  have hd1_ne : (↑d : ℚ) + 1 ≠ 0 := by positivity
  have heq : (1 : ℚ) - 1 / (↑d + 1) = ↑d / (↑d + 1) := by field_simp [hd1_ne]; ring
  rw [heq]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: GENERAL MAXIMUM THEOREM
-- ═══════════════════════════════════════════════════════════════════

/-- **Main Theorem**: T(d) = max { x · (1-x)^d : x ∈ [0,1] }.

    For all x ∈ [0,1] and d ≥ 1: x * (1-x)^d ≤ T(d) = d^d/(d+1)^{d+1}.

    Proof (AM-GM over ℝ, then cast to ℚ):
    Let t = (d+1)*x ∈ [0, d+1]. Then x*(1-x)^d = t*(d+1-t)^d/(d+1)^{d+1}.
    Apply AM-GM to d+1 numbers: t, (d+1-t)/d (× d copies).
    - Sum = d+1, AM = 1.
    - GM = (t · ((d+1-t)/d)^d)^{1/(d+1)}.
    - AM ≥ GM: 1 ≥ t · (d+1-t)^d / d^d, i.e., t · (d+1-t)^d ≤ d^d.
    - Dividing by (d+1)^{d+1}: x*(1-x)^d ≤ d^d/(d+1)^{d+1} = T(d). -/
theorem lllThreshold_is_maximum (d : ℕ) (hd : 0 < d) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x)^d ≤ lllThreshold d := by
  -- Cast to ℝ: ℚ → ℝ is order-preserving, prove the ℝ version
  have key : ((x * (1 - x) ^ d : ℚ) : ℝ) ≤ ((lllThreshold d : ℚ) : ℝ) := by
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
    simp only [lllThreshold, if_neg (Nat.pos_iff_ne_zero.mp hd)]
    push_cast
    set xr : ℝ := (x : ℝ) with hxr_def
    set dr : ℝ := (d : ℝ) with hdr_def
    have hxr : 0 ≤ xr := by rw [hxr_def]; exact_mod_cast hx
    have hx1r : xr ≤ 1 := by rw [hxr_def]; exact_mod_cast hx1
    have hdr : 0 < dr := by rw [hdr_def]; exact_mod_cast hd
    have hd1r : 0 < dr + 1 := by linarith
    -- p₂ nonnegativity: 0 ≤ (1-xr)/dr follows from xr ≤ 1 and dr > 0
    have hp2_nn : 0 ≤ (1 - xr) / dr := div_nonneg (by linarith) hdr.le
    -- Step 1: Weighted AM-GM: xr^{1/(dr+1)} * ((1-xr)/dr)^{dr/(dr+1)} ≤ 1/(dr+1)
    have h_amgm : xr ^ (1 / (dr + 1)) * ((1 - xr) / dr) ^ (dr / (dr + 1)) ≤ 1 / (dr + 1) := by
      have h := Real.geom_mean_le_arith_mean2_weighted
        (w₁ := 1 / (dr + 1)) (w₂ := dr / (dr + 1))
        (p₁ := xr) (p₂ := (1 - xr) / dr)
        (by positivity) (by positivity) hxr hp2_nn
        (by field_simp [hd1r.ne']; ring)
      linarith [show 1 / (dr + 1) * xr + dr / (dr + 1) * ((1 - xr) / dr) = 1 / (dr + 1)
        from by field_simp [hdr.ne', hd1r.ne']; ring]
    -- Step 2: rpow identity: (xr * ((1-xr)/dr)^d)^{1/(dr+1)} = xr^{1/(dr+1)} * ((1-xr)/dr)^{dr/(dr+1)}
    have h_eq : (xr * ((1 - xr) / dr) ^ d) ^ (1 / (dr + 1)) =
        xr ^ (1 / (dr + 1)) * ((1 - xr) / dr) ^ (dr / (dr + 1)) := by
      rw [Real.mul_rpow hxr (pow_nonneg hp2_nn d)]
      congr 1
      rw [← Real.rpow_natCast ((1 - xr) / dr) d, ← Real.rpow_mul hp2_nn]
      congr 1; push_cast; ring
    -- Step 3: Raise to (dr+1)-th power: xr * ((1-xr)/dr)^d ≤ (1/(dr+1))^{d+1}
    have h_prod_le : xr * ((1 - xr) / dr) ^ d ≤ (1 / (dr + 1)) ^ (d + 1) := by
      have hlhs : 0 ≤ xr * ((1 - xr) / dr) ^ d := mul_nonneg hxr (pow_nonneg hp2_nn d)
      have h_le : (xr * ((1 - xr) / dr) ^ d) ^ (1 / (dr + 1)) ≤ 1 / (dr + 1) :=
        h_eq ▸ h_amgm
      -- Convert nat pow (d+1) to rpow (dr+1) so we can use Real.rpow_le_rpow
      have hrpow_nat : (1 / (dr + 1)) ^ (d + 1) = (1 / (dr + 1)) ^ (dr + 1) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast; ring
      rw [hrpow_nat]
      calc xr * ((1 - xr) / dr) ^ d
          = ((xr * ((1 - xr) / dr) ^ d) ^ (1 / (dr + 1))) ^ (dr + 1) := by
            rw [← Real.rpow_mul hlhs, div_mul_cancel₀ _ hd1r.ne', Real.rpow_one]
        _ ≤ (1 / (dr + 1)) ^ (dr + 1) :=
            Real.rpow_le_rpow (by positivity) h_le (le_of_lt hd1r)
    -- Step 4: xr*(1-xr)^d = xr*((1-xr)/dr)^d * dr^d ≤ (1/(dr+1))^{d+1} * dr^d = dr^d/(dr+1)^{d+1}
    have hpow_d : 0 < dr ^ d := pow_pos hdr _
    have hrewrite : xr * (1 - xr) ^ d = xr * ((1 - xr) / dr) ^ d * dr ^ d := by
      have hcancel : ((1 - xr) / dr) ^ d * dr ^ d = (1 - xr) ^ d :=
        by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero d hdr.ne')]
      rw [mul_assoc, hcancel]
    rw [hrewrite]
    calc xr * ((1 - xr) / dr) ^ d * dr ^ d
        ≤ (1 / (dr + 1)) ^ (d + 1) * dr ^ d :=
            mul_le_mul_of_nonneg_right h_prod_le hpow_d.le
      _ = dr ^ d / (dr + 1) ^ (d + 1) := by
            rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
  exact_mod_cast key

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: ALGEBRAIC TIGHTNESS COROLLARY
-- ═══════════════════════════════════════════════════════════════════

/-- **Algebraic Tightness**: If p > T(d), then no x ∈ [0,1] satisfies
    the symmetric LLL condition p ≤ x * (1-x)^d.

    This is the algebraic lower bound: the symmetric LLL threshold T(d)
    cannot be lowered while maintaining the algebraic structure. -/
theorem lll_threshold_tight (d : ℕ) (hd : 0 < d) (p : ℚ) (hp : lllThreshold d < p) :
    ∀ x : ℚ, 0 ≤ x → x ≤ 1 → ¬ (p ≤ x * (1 - x)^d) := by
  intro x hx hx1 hcontra
  have hmax := lllThreshold_is_maximum d hd x hx hx1
  linarith

/-- **No slack removal**: If the LLL condition holds at equality
    (prob = T(d)), then any strictly larger probability is infeasible.
    T(d) is the precise algebraic threshold. -/
theorem lll_threshold_no_improvement (d : ℕ) (hd : 0 < d) (ε : ℚ) (hε : 0 < ε) :
    ∀ x : ℚ, 0 ≤ x → x ≤ 1 → ¬ (lllThreshold d + ε ≤ x * (1 - x)^d) := by
  intro x hx hx1 hcontra
  have hmax := lllThreshold_is_maximum d hd x hx hx1
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: LLL TIGHTNESS — CHARACTERIZATION OF OPTIMAL ASSIGNMENT
-- ═══════════════════════════════════════════════════════════════════

/-- The assignment x = 1/(d+1) is the unique maximizer: for all x ≠ 1/(d+1),
    x * (1-x)^d < T(d) (strict inequality). -/
theorem lllThreshold_strict_maximum (d : ℕ) (hd : 0 < d) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hne : x ≠ 1 / (↑d + 1)) :
    x * (1 - x)^d < lllThreshold d := by
  -- Direct proof via strict AM-GM: x ≠ 1/(d+1) ↔ weighted AM-GM is strict
  have key : ((x * (1 - x) ^ d : ℚ) : ℝ) < ((lllThreshold d : ℚ) : ℝ) := by
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast,
               lllThreshold, if_neg (Nat.pos_iff_ne_zero.mp hd)]
    push_cast
    set xr : ℝ := (x : ℝ)
    set dr : ℝ := (d : ℝ)
    have hxr : 0 ≤ xr := by exact_mod_cast hx
    have hx1r : xr ≤ 1 := by exact_mod_cast hx1
    have hdr : 0 < dr := by exact_mod_cast hd
    have hd1r : 0 < dr + 1 := by linarith
    have hp2_nn : 0 ≤ (1 - xr) / dr := div_nonneg (by linarith) hdr.le
    -- Key: xr ≠ (1-xr)/dr because x ≠ 1/(d+1)
    have hne_r : xr ≠ (1 - xr) / dr := by
      intro heq
      have h1 : 1 - xr = xr * dr := (div_eq_iff hdr.ne').mp heq.symm
      have hxeq : xr = 1 / (dr + 1) := by
        rw [eq_comm, div_eq_iff hd1r.ne']
        linarith [show xr * (dr + 1) = xr * dr + xr from by ring, h1]
      have hx_cast : (x : ℝ) = 1 / ((d : ℝ) + 1) := hxeq
      exact hne (by exact_mod_cast hx_cast)
    -- Strict weighted AM-GM on Fin 2 finset
    have hstrict : xr ^ (1 / (dr + 1)) * ((1 - xr) / dr) ^ (dr / (dr + 1)) < 1 / (dr + 1) := by
      have hlt := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos Finset.univ
          (![1 / (dr + 1), dr / (dr + 1)] : Fin 2 → ℝ)
          (![xr, (1 - xr) / dr] : Fin 2 → ℝ)
          (by intro i _; fin_cases i <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
              positivity)
          (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                         Matrix.head_cons]; field_simp [hd1r.ne']; ring)
          (by intro i _; fin_cases i <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
              [exact hxr; exact hp2_nn])).mpr
          ⟨0, Finset.mem_univ _, 1, Finset.mem_univ _, by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
            exact hne_r⟩
      simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons] at hlt
      have hAM : 1 / (dr + 1) * xr + dr / (dr + 1) * ((1 - xr) / dr) = 1 / (dr + 1) := by
        field_simp [hdr.ne', hd1r.ne']; ring
      linarith
    -- rpow identity: (xr * ((1-xr)/dr)^d)^{1/(dr+1)} = GM
    have h_eq : (xr * ((1 - xr) / dr) ^ d) ^ (1 / (dr + 1)) =
        xr ^ (1 / (dr + 1)) * ((1 - xr) / dr) ^ (dr / (dr + 1)) := by
      rw [Real.mul_rpow hxr (pow_nonneg hp2_nn d),
          ← Real.rpow_natCast ((1 - xr) / dr) d, ← Real.rpow_mul hp2_nn]
      congr 1; push_cast; ring
    have hlhs_nn : 0 ≤ xr * ((1 - xr) / dr) ^ d := mul_nonneg hxr (pow_nonneg hp2_nn d)
    -- Raise strict inequality to (dr+1)-th power
    have h_prod_lt : xr * ((1 - xr) / dr) ^ d < (1 / (dr + 1)) ^ (d + 1) := by
      have hrpow_nat : (1 / (dr + 1)) ^ (d + 1) = (1 / (dr + 1)) ^ (dr + 1) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast; ring
      rw [hrpow_nat]
      calc xr * ((1 - xr) / dr) ^ d
          = ((xr * ((1 - xr) / dr) ^ d) ^ (1 / (dr + 1))) ^ (dr + 1) := by
            rw [← Real.rpow_mul hlhs_nn, div_mul_cancel₀ _ hd1r.ne', Real.rpow_one]
        _ = (xr ^ (1 / (dr + 1)) * ((1 - xr) / dr) ^ (dr / (dr + 1))) ^ (dr + 1) := by
            rw [h_eq]
        _ < (1 / (dr + 1)) ^ (dr + 1) := Real.rpow_lt_rpow (by positivity) hstrict hd1r
    -- Multiply by dr^d to recover xr*(1-xr)^d
    calc xr * (1 - xr) ^ d
        = xr * ((1 - xr) / dr) ^ d * dr ^ d := by
          rw [mul_assoc, div_pow, div_mul_cancel₀ _ (pow_ne_zero d hdr.ne')]
      _ < (1 / (dr + 1)) ^ (d + 1) * dr ^ d :=
          mul_lt_mul_of_pos_right h_prod_lt (pow_pos hdr d)
      _ = dr ^ d / (dr + 1) ^ (d + 1) := by rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
  exact_mod_cast key

/-- The threshold T(d) satisfies a fixed-point equation:
    T(d) = 1/(d+1) · (1 - 1/(d+1))^d.
    This is the basis of the "threshold_satisfies_lll" proof in the parent. -/
theorem lllThreshold_fixed_point (d : ℕ) (hd : 0 < d) :
    lllThreshold d = 1 / (↑d + 1) * (1 - 1 / (↑d + 1))^d := by
  rw [← lllThreshold_achieved d hd]

/-- Summary: The symmetric LLL condition p ≤ T(d) is algebraically tight.
    - **Upper bound** (this file): ∃ x ∈ [0,1] with p ≤ x*(1-x)^d ↔ p ≤ T(d).
    - **Lower bound** (lll_threshold_tight): p > T(d) → no x works.
    Together: T(d) is the exact algebraic threshold.

    **Proof**:
    (→) The witness x = 1/(d+1) achieves x*(1-x)^d = T(d) ≥ p. (proved)
    (←) If such x exists, then p ≤ x*(1-x)^d ≤ T(d) by lllThreshold_is_maximum. (sorry) -/
theorem lllThreshold_exact_algebraic_threshold (d : ℕ) (hd : 0 < d) (p : ℚ) (hp : 0 ≤ p) :
    (∃ x : ℚ, 0 ≤ x ∧ x ≤ 1 ∧ p ≤ x * (1 - x)^d) ↔ p ≤ lllThreshold d := by
  constructor
  · -- (←) Witness x = 1/(d+1) achieves T(d): p ≤ T(d) = x*(1-x)^d
    intro ⟨x, hx, hx1, hle⟩
    exact le_trans hle (lllThreshold_is_maximum d hd x hx hx1)
  · -- (→) Use x* = 1/(d+1) as witness; it achieves the maximum
    intro hle
    have hd1_pos : (0 : ℚ) < (d : ℚ) + 1 := by exact_mod_cast Nat.succ_pos d
    have hnn : (0 : ℚ) ≤ 1 / ((d : ℚ) + 1) :=
      div_nonneg (by norm_num : (0:ℚ) ≤ 1) hd1_pos.le
    refine ⟨1 / ((d : ℚ) + 1), hnn, ?_, ?_⟩
    · have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
      rw [div_le_one hd1_pos]; linarith
    · rw [lllThreshold_achieved d hd]; exact hle

end ProbMethod.LovaszLocal.OQ02
