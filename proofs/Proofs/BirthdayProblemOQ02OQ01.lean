import Mathlib

/-
# Matching Lower Bound for Birthday Problem (OQ-02-OQ-01)

## What This Proves
Formalizes the matching lower bound for the Birthday Problem:

  P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))

Combined with the upper bound from OQ-02 (P(all distinct) ≤ exp(-k(k-1)/(2d))),
this gives a two-sided exponential approximation for the birthday collision probability.

## Key Mathematical Idea
For 0 ≤ x ≤ 1/2, we have ln(1-x) ≥ -x - x² (a consequence of the Taylor series).
Applied to each factor (1 - i/d) in P(all distinct) = ∏(1-i/d):

  ln(∏(1-i/d)) = ∑ ln(1-i/d) ≥ ∑(-i/d - i²/d²) = -k(k-1)/(2d) - S₂/d²

where S₂ = ∑ i² = k(k-1)(2k-1)/6 ≤ k²(k-1)²/4.

## Approach
- **Foundation:** The key inequality ln(1-x) ≥ -x - x² for 0 ≤ x ≤ 1/2
- **Product bound:** Apply to each factor and sum logarithms
- **Exponentiate:** Obtain the exponential lower bound on the product

## Note on the x ≤ 1/2 constraint
The inequality exp(-x - x²) ≤ 1 - x is FALSE for x near 1 (e.g., at x = 0.9,
exp(-1.71) ≈ 0.18 > 0.1 = 1 - 0.9). It holds for 0 ≤ x ≤ 1/2 by a monotonicity
argument: g(x) = (1-x)·exp(x+x²) has g(0) = 1 and g'(x) = exp(x+x²)·x(1-2x) ≥ 0
on [0, 1/2], so g(x) ≥ 1. The constraint 2(k-1) ≤ d in the main theorem ensures
each factor i/d ≤ 1/2, which covers the standard birthday paradox regime (k ≈ √d).
-/

open Finset Real

/- ## Core Inequality: ln(1-x) ≥ -x - x² for 0 ≤ x ≤ 1/2 -/

/-- For 0 ≤ x ≤ 1/2, we have 1 - x ≥ exp(-x - x²).
    Equivalently, ln(1-x) ≥ -x - x².

    Proof: Let g(x) = (1-x)·exp(x+x²). Then g(0) = 1 and
    g'(x) = exp(x+x²)·x(1-2x) ≥ 0 on [0, 1/2], so g(x) ≥ 1.
    We formalize this using the Taylor bound exp(t) ≥ 1 + t + t²/2
    (from Mathlib's `sum_le_exp_of_nonneg`), which reduces the
    transcendental inequality to polynomial arithmetic. -/
theorem exp_neg_sub_sq_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : 2 * x ≤ 1) :
    Real.exp (-x - x ^ 2) ≤ 1 - x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hxx : (0 : ℝ) ≤ x + x ^ 2 := by nlinarith [sq_nonneg x]
  -- Taylor bound: exp(t) ≥ 1 + t + t²/2 for t = x + x² ≥ 0
  have h_taylor := Real.sum_le_exp_of_nonneg hxx 3
  -- Simplify the partial sum to 1 + (x+x²) + (x+x²)²/2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    pow_zero, pow_one, Nat.cast_one, Nat.cast_ofNat, zero_add, div_one] at h_taylor
  -- h_taylor : 1 + (x + x²) + (x + x²)² / 2 ≤ exp(x + x²)
  -- Key polynomial inequality:
  -- (1-x)(1 + (x+x²) + (x+x²)²/2) - 1 = x²·((1-2x)(1+x) + x²(1-x))/2 ≥ 0
  have h_poly : 1 ≤ (1 - x) * (1 + (x + x ^ 2) + (x + x ^ 2) ^ 2 / 2) := by
    have ha : 0 ≤ (1 - 2 * x) * (1 + x) := mul_nonneg (by linarith) (by linarith)
    have hb : 0 ≤ x ^ 2 * (1 - x) := mul_nonneg (sq_nonneg x) (by linarith)
    nlinarith [sq_nonneg x, sq_nonneg (x * (1 + x)), ha, hb]
  -- Chain: 1 ≤ (1-x)·poly ≤ (1-x)·exp(x+x²)
  have h_main : 1 ≤ (1 - x) * Real.exp (x + x ^ 2) :=
    le_trans h_poly (mul_le_mul_of_nonneg_left h_taylor h1x.le)
  -- Convert: exp(-(x+x²)) ≤ 1-x via exp(-t)·exp(t) = 1
  rw [show -x - x ^ 2 = -(x + x ^ 2) from by ring]
  have heu := Real.exp_pos (x + x ^ 2)
  have hprod : Real.exp (-(x + x ^ 2)) * Real.exp (x + x ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_times : Real.exp (-(x + x ^ 2)) * Real.exp (x + x ^ 2)
      ≤ (1 - x) * Real.exp (x + x ^ 2) := by rw [hprod]; exact h_main
  exact (mul_le_mul_right heu).mp h_times

/-- The product formula for the probability that k items are all distinct
    among d possibilities. P(all distinct) = ∏_{i=0}^{k-1} (1 - i/d). -/
noncomputable def birthdayProduct (k d : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (d : ℝ))

/-- Each factor in the birthday product is nonneg when k ≤ d + 1. -/
theorem birthdayProduct_factor_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1)
    (i : ℕ) (hi : i ∈ Finset.range k) : 0 ≤ 1 - (i : ℝ) / (d : ℝ) := by
  rw [Finset.mem_range] at hi
  have : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : i ≤ d)
  have hid : (i : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hd : (0 : ℝ) < d)]
    exact this
  linarith

/-- Each factor in the birthday product is at most 1. -/
theorem birthdayProduct_factor_le_one {d : ℕ} (hd : 0 < d)
    (i : ℕ) : 1 - (i : ℝ) / (d : ℝ) ≤ 1 := by
  have : 0 ≤ (i : ℝ) / (d : ℝ) := div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg d)
  linarith

/-- The birthday product is nonneg when k ≤ d + 1. -/
theorem birthdayProduct_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    0 ≤ birthdayProduct k d :=
  Finset.prod_nonneg (fun i hi => birthdayProduct_factor_nonneg hd hk i hi)

/- ## Sum of squares bound -/

/-- The sum ∑_{i<k} i² = k(k-1)(2k-1)/6. -/
theorem sum_sq_formula (k : ℕ) :
    6 * ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 = (k : ℝ) * (k - 1) * (2 * k - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- Bound: ∑_{i<k} i² ≤ k²(k-1)²/4 for k ≥ 1.
    (This follows from k(k-1)(2k-1)/6 ≤ k²(k-1)²/4, i.e., 2(2k-1)/3 ≤ k(k-1).) -/
theorem sum_sq_le_quartic (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (k - 1) ^ 2 / 4 := by
  -- From sum_sq_formula: 6·∑i² = k(k-1)(2k-1)
  -- Need: k(k-1)(2k-1)/6 ≤ k²(k-1)²/4, i.e., 4(2k-1) ≤ 6k(k-1) for k ≥ 2
  have hsf := sum_sq_formula k
  -- Express ∑i² from the formula
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  have hsum : ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 = (k : ℝ) * (k - 1) * (2 * k - 1) / 6 := by
    linarith
  rw [hsum]
  -- Need: k(k-1)(2k-1)/6 ≤ k²(k-1)²/4
  -- Equivalently: 4k(k-1)(2k-1) ≤ 6k²(k-1)² = 6k(k-1)·k(k-1)
  -- For k ≥ 2: cancel k(k-1) > 0 to get 4(2k-1) ≤ 6k(k-1)
  -- For k = 1: both sides are 0
  rcases Nat.eq_or_gt_of_le hk with rfl | hk2
  · simp
  · push_cast
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    nlinarith [sq_nonneg ((k : ℝ) - 2), sq_nonneg ((k : ℝ) - 1)]

/- ## Gauss sum for the exponent -/

/-- The Gauss sum: ∑_{i<k} i = k(k-1)/2. -/
private theorem gauss_sum (k : ℕ) :
    ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/- ## Main Lower Bound -/

/-- **Main Theorem**: Birthday product lower bound.
    P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))
    for 1 ≤ k, 1 ≤ d, 2(k-1) ≤ d.

    The constraint 2(k-1) ≤ d ensures each factor i/d ≤ 1/2,
    which is needed for the core inequality. This covers the standard
    birthday paradox regime where k ≈ √d (since √d ≪ d/2).

    This is the matching lower bound for the OQ-02 upper bound:
    P(all distinct) ≤ exp(-k(k-1)/(2d)). -/
theorem birthdayProduct_lower_bound {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : k ≤ d + 1) (hkd2 : 2 * (k - 1) ≤ d) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d := by
  unfold birthdayProduct
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  -- Step 1: Each factor (1 - i/d) ≥ exp(-i/d - (i/d)²)
  have h_factor : ∀ i ∈ Finset.range k,
      Real.exp (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2) ≤ 1 - ↑i / ↑d := by
    intro i hi; rw [Finset.mem_range] at hi
    apply exp_neg_sub_sq_le_one_sub
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · -- 2 * (i/d) ≤ 1 since 2*i ≤ 2*(k-1) ≤ d
      have hi2d : 2 * i ≤ d := by omega
      rw [show 2 * ((↑i : ℝ) / ↑d) = (2 * ↑i : ℝ) / ↑d from by ring,
          div_le_one hd_pos]
      exact_mod_cast hi2d
  -- Step 2: Product of exp ≤ product of (1 - i/d)
  have h_prod : ∏ i ∈ Finset.range k, Real.exp (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2)
      ≤ ∏ i ∈ Finset.range k, (1 - ↑i / ↑d) :=
    Finset.prod_le_prod (fun i _ => le_of_lt (Real.exp_pos _)) h_factor
  -- Step 3: Product of exp = exp of sum
  have h_exp_sum : ∏ i ∈ Finset.range k, Real.exp (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2)
      = Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2)) := by
    rw [← Real.exp_sum]
  -- Step 4: The exponent of the target ≤ the sum (monotonicity of exp)
  -- Sum = -∑(i/d) - ∑(i/d)² = -k(k-1)/(2d) - (∑i²)/d²
  -- Target exponent = -k(k-1)/(2d) - k²(k-1)²/(4d²)
  -- Since ∑i² ≤ k²(k-1)²/4 (sum_sq_le_quartic), we get target ≤ sum.
  have h_exponent : -(↑k : ℝ) * (↑k - 1) / (2 * ↑d) -
      (↑k : ℝ) ^ 2 * (↑k - 1) ^ 2 / (4 * (↑d : ℝ) ^ 2)
      ≤ ∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2) := by
    -- Rewrite each summand: -i/d - (i/d)² = -i/d - i²/d²
    simp_rw [show ∀ i : ℕ, -(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2 =
        -(↑i : ℝ) / ↑d - (↑i : ℝ) ^ 2 / (↑d : ℝ) ^ 2 from fun i => by ring]
    -- Split the sum: ∑(f - g) = ∑f - ∑g
    rw [Finset.sum_sub_distrib]
    -- Simplify first sum: ∑(-i/d) = -k(k-1)/(2d)
    have h_first : ∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d) =
        -(↑k : ℝ) * (↑k - 1) / (2 * ↑d) := by
      rw [show ∀ i : ℕ, -(↑i : ℝ) / (↑d : ℝ) = -(1 / ↑d) * ↑i from fun i => by ring]
      rw [← Finset.mul_sum, gauss_sum]; ring
    -- Factor second sum: ∑(i²/d²) = (∑i²)/d²
    have h_second : ∑ i ∈ Finset.range k, ((↑i : ℝ) ^ 2 / (↑d : ℝ) ^ 2) =
        (∑ i ∈ Finset.range k, (↑i : ℝ) ^ 2) / (↑d : ℝ) ^ 2 :=
      (Finset.sum_div ..).symm
    rw [h_first, h_second]
    -- Now: -K - Q ≤ -K - S/d² where Q = k²(k-1)²/(4d²), S = ∑i²
    -- From sum_sq_le_quartic: S ≤ k²(k-1)²/4, so S/d² ≤ k²(k-1)²/(4d²) = Q
    have hd2_nn : (0 : ℝ) ≤ (↑d : ℝ) ^ 2 := by positivity
    have h_sq := sum_sq_le_quartic k hk
    have h_div := div_le_div_of_nonneg_right h_sq hd2_nn
    -- h_div : S/d² ≤ (k²(k-1)²/4)/d², which equals k²(k-1)²/(4d²) by ring
    have h_eq : (↑k : ℝ) ^ 2 * (↑k - 1) ^ 2 / 4 / (↑d : ℝ) ^ 2 =
        (↑k : ℝ) ^ 2 * (↑k - 1) ^ 2 / (4 * (↑d : ℝ) ^ 2) := by ring
    linarith [h_eq ▸ h_div]
  -- Chain: exp(target) ≤ exp(∑...) = ∏ exp(...) ≤ ∏ (1 - i/d)
  calc Real.exp (-(↑k : ℝ) * (↑k - 1) / (2 * ↑d) -
      (↑k : ℝ) ^ 2 * (↑k - 1) ^ 2 / (4 * (↑d : ℝ) ^ 2))
      ≤ Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2)) :=
        Real.exp_le_exp.mpr h_exponent
    _ = ∏ i ∈ Finset.range k, Real.exp (-(↑i : ℝ) / ↑d - (↑i / ↑d) ^ 2) :=
        h_exp_sum.symm
    _ ≤ ∏ i ∈ Finset.range k, (1 - ↑i / ↑d) := h_prod

/-- The two-sided bound: combining with the upper bound from OQ-02,
    P(all distinct) is sandwiched between two exponentials.
    This gives a precise asymptotic: P(all distinct) ≈ exp(-k(k-1)/(2d)).

    The constraint 2(k-1) ≤ d is for the lower bound; the upper bound
    holds for all k ≤ d + 1. For the birthday paradox (k ≈ √d), this
    constraint is easily satisfied since √d ≪ d/2. -/
theorem birthdayProduct_two_sided {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd2 : 2 * (k - 1) ≤ d) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d ∧
    birthdayProduct k d ≤ Real.exp (-(k : ℝ) * (k - 1) / (2 * d)) := by
  have hkd : k ≤ d + 1 := by omega
  exact ⟨birthdayProduct_lower_bound hd hk hkd hkd2, by
    -- Upper bound from OQ-02 (Erdős-style: 1-x ≤ exp(-x))
    unfold birthdayProduct
    calc ∏ i ∈ Finset.range k, (1 - (i : ℝ) / d)
        ≤ ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / d) := by
          apply Finset.prod_le_prod
            (fun i hi => birthdayProduct_factor_nonneg (by omega) hkd i hi)
          intro i _
          have h := add_one_le_exp (-↑i / (↑d : ℝ))
          have : -↑i / (↑d : ℝ) + 1 = 1 - ↑i / ↑d := by ring
          linarith
      _ = Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d)) := by
          rw [Real.exp_sum]
      _ = Real.exp (-(↑k : ℝ) * (↑k - 1) / (2 * ↑d)) := by
          congr 1
          -- ∑_{i<k} (-i/d) = -(1/d) · ∑_{i<k} i = -(1/d) · k(k-1)/2
          rw [show ∀ i : ℕ, -(↑i : ℝ) / ↑d = -(1 / ↑d) * ↑i from fun i => by ring]
          rw [← Finset.mul_sum]
          rw [show ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * (↑k - 1) / 2 from by
            have := Finset.sum_range_id_eq_sum_range_succ_div_two k
            push_cast at this ⊢
            linarith]
          ring
  ⟩
