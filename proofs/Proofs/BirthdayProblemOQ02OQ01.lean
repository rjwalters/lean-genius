import Mathlib

/-
# Matching Lower Bound for Birthday Problem (OQ-02-OQ-01)

## What This Proves
Formalizes the matching lower bound for the Birthday Problem:

  P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))

Combined with the upper bound from OQ-02 (P(all distinct) ≤ exp(-k(k-1)/(2d))),
this gives a two-sided exponential approximation for the birthday collision probability.

## Key Mathematical Idea
For 0 ≤ x ≤ 1/2, we have ln(1-x) ≥ -x - x² (from Taylor with remainder).
Applied to each factor (1 - i/d) in P(all distinct) = ∏(1-i/d):

  ln(∏(1-i/d)) = ∑ ln(1-i/d) ≥ ∑(-i/d - i²/d²) = -k(k-1)/(2d) - S₂/d²

where S₂ = ∑ i² = k(k-1)(2k-1)/6 ≤ k²(k-1)²/4.

## Important: Hypothesis on k
The core inequality ln(1-x) ≥ -x - x² requires x ≤ 1/2. For the birthday product,
this means each factor ratio i/d ≤ 1/2, i.e., (k-1)/d ≤ 1/2, i.e., 2(k-1) ≤ d.
This covers the birthday problem's regime of interest (k ~ √d ≪ d).
-/

open Finset Real

/- ## Core Inequality: ln(1-x) ≥ -x - x² for 0 ≤ x ≤ 1/2 -/

/-- For 0 ≤ x ≤ 1/2, we have 1 - x ≥ exp(-x - x²).
    Equivalently, ln(1-x) ≥ -x - x².

    Proof: From exp(y) ≥ 1 + y + y²/2 (Taylor, via `sum_le_exp_of_nonneg`),
    with y = x + x²: (1-x) · exp(x+x²) ≥ (1-x)(1 + (x+x²) + (x+x²)²/2) ≥ 1.
    The last step uses the algebraic identity that the expanded polynomial
    equals 1 + x²(1-x-x²-x³)/2 ≥ 1 for x ∈ [0, 1/2].

    Note: The inequality FAILS for x close to 1 (e.g., x = 0.9). -/
theorem exp_neg_sub_sq_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-x - x ^ 2) ≤ 1 - x := by
  have h1mx_pos : (0 : ℝ) < 1 - x := by linarith
  set y := x + x ^ 2 with hy_def
  have hy_nn : 0 ≤ y := by positivity
  -- Step 1: exp(y) ≥ 1 + y + y²/2 from Taylor (n=3 partial sum)
  have hT := Real.sum_le_exp_of_nonneg hy_nn 3
  -- Simplify the partial sum: ∑_{i<3} y^i/i! = 1 + y + y²/2
  have hps : ∑ i ∈ Finset.range 3, y ^ i / (↑(Nat.factorial i) : ℝ) =
      1 + y + y ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
      Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, pow_succ]
    ring
  rw [hps] at hT
  -- hT : 1 + y + y^2/2 ≤ exp(y)
  -- Step 2: (1-x)(1 + y + y²/2) ≥ 1
  -- After expanding y = x+x², this is 1 + x²(1-x-x²-x³)/2 ≥ 1
  have key : 1 ≤ (1 - x) * (1 + y + y ^ 2 / 2) := by
    rw [hy_def]
    -- Need: 1 ≤ (1-x)(1 + (x+x²) + (x+x²)²/2)
    -- This expands to 1 + x²/2 - x³/2 - x⁴/2 - x⁵/2
    -- For x ∈ [0, 1/2], the polynomial part x²(1-x-x²-x³)/2 ≥ 0
    have hx2 : x * x ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left hx1 hx0
    have hx3 : x * x * x ≤ x * x * (1 / 2) := mul_le_mul_of_nonneg_left hx1 (by nlinarith)
    nlinarith [sq_nonneg x, sq_nonneg (x * x)]
  -- Step 3: (1-x) * exp(y) ≥ 1
  have h_prod : 1 ≤ (1 - x) * Real.exp y := by
    calc (1 : ℝ) ≤ (1 - x) * (1 + y + y ^ 2 / 2) := key
      _ ≤ (1 - x) * Real.exp y :=
          mul_le_mul_of_nonneg_left hT (le_of_lt h1mx_pos)
  -- Step 4: exp(-y) ≤ 1-x
  rw [show -x - x ^ 2 = -y from by rw [hy_def]; ring, Real.exp_neg, inv_eq_one_div]
  rw [div_le_iff (Real.exp_pos y)]
  linarith

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
  have hsf := sum_sq_formula k
  have hsum : ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 = (k : ℝ) * (k - 1) * (2 * k - 1) / 6 := by
    linarith
  rw [hsum]
  rcases Nat.eq_or_gt_of_le hk with rfl | hk2
  · simp
  · push_cast
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    nlinarith [sq_nonneg ((k : ℝ) - 2), sq_nonneg ((k : ℝ) - 1)]

/- ## Main Lower Bound -/

/-- **Main Theorem**: Birthday product lower bound.
    P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))
    for 1 ≤ k, d ≥ 1, and 2(k-1) ≤ d.

    The constraint 2(k-1) ≤ d ensures each ratio i/d ≤ 1/2, which is needed
    for the core inequality ln(1-x) ≥ -x-x². This covers the birthday problem's
    regime of interest where k ~ √d.

    This is the matching lower bound for the OQ-02 upper bound:
    P(all distinct) ≤ exp(-k(k-1)/(2d)). -/
theorem birthdayProduct_lower_bound {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : 2 * (k - 1) ≤ d) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d := by
  -- Each factor: 1 - i/d ≥ exp(-i/d - (i/d)²) by exp_neg_sub_sq_le_one_sub
  -- since i/d ≤ (k-1)/d ≤ 1/2
  unfold birthdayProduct
  -- Lower bound each factor, then use exp_sum
  calc Real.exp (-(k : ℝ) * (k - 1) / (2 * d) -
          (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d - ((↑i : ℝ) / ↑d) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        -- Need: -k(k-1)/(2d) - k²(k-1)²/(4d²) ≤ ∑(-i/d - i²/d²)
        -- LHS = -∑i/d - k²(k-1)²/(4d²), RHS = -∑i/d - ∑i²/d²
        -- So need: k²(k-1)²/(4d²) ≥ ∑i²/d²
        -- i.e., ∑i² ≤ k²(k-1)²/4 (from sum_sq_le_quartic)
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        have hd_sq_pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
        -- Compute ∑(-i/d - i²/d²) = -∑i/d - ∑i²/d²
        have hsum_split : ∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d - ((↑i : ℝ) / ↑d) ^ 2) =
            -(∑ i ∈ Finset.range k, (↑i : ℝ)) / ↑d -
            (∑ i ∈ Finset.range k, (↑i : ℝ) ^ 2) / (↑d) ^ 2 := by
          simp only [div_pow, neg_div]
          rw [← Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_div]
          congr 1
          ext i; ring
        rw [hsum_split]
        -- ∑i = k(k-1)/2
        have hgauss : ∑ i ∈ Finset.range k, (↑i : ℝ) = (↑k : ℝ) * (↑k - 1) / 2 := by
          have := Finset.sum_range_id_eq_sum_range_succ_div_two k
          push_cast at this ⊢; linarith
        rw [hgauss]
        -- Now need: -k(k-1)/(2d) - k²(k-1)²/(4d²) ≤ -k(k-1)/2/d - ∑i²/d²
        -- i.e., k²(k-1)²/(4d²) ≥ ∑i²/d²
        -- i.e., ∑i² ≤ k²(k-1)²/4
        have hsq := sum_sq_le_quartic k hk
        have : (∑ i ∈ Finset.range k, (↑i : ℝ) ^ 2) / (↑d) ^ 2 ≤
            (↑k : ℝ) ^ 2 * (↑k - 1) ^ 2 / 4 / (↑d) ^ 2 :=
          div_le_div_of_nonneg_right hsq (le_of_lt hd_sq_pos)
        linarith
    _ = ∏ i ∈ Finset.range k, Real.exp (-(↑i : ℝ) / ↑d - ((↑i : ℝ) / ↑d) ^ 2) := by
        rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.range k, (1 - (↑i : ℝ) / ↑d) := by
        apply Finset.prod_le_prod
        · intro i _
          exact le_of_lt (Real.exp_pos _)
        · intro i hi
          rw [Finset.mem_range] at hi
          apply exp_neg_sub_sq_le_one_sub
          · exact div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg d)
          · -- i/d ≤ (k-1)/d ≤ 1/2
            rw [div_le_div_iff (by exact_mod_cast (show 0 < d by omega) : (0:ℝ) < d)
                               (by norm_num : (0:ℝ) < 2)]
            push_cast
            have : (i : ℤ) ≤ k - 1 := by omega
            have : 2 * ((k : ℤ) - 1) ≤ d := by exact_mod_cast hkd
            linarith

/-- The two-sided bound: combining with the upper bound from OQ-02,
    P(all distinct) is sandwiched between two exponentials.
    This gives a precise asymptotic: P(all distinct) ≈ exp(-k(k-1)/(2d)). -/
theorem birthdayProduct_two_sided {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : 2 * (k - 1) ≤ d) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d ∧
    birthdayProduct k d ≤ Real.exp (-(k : ℝ) * (k - 1) / (2 * d)) := by
  have hkd' : k ≤ d + 1 := by omega
  exact ⟨birthdayProduct_lower_bound hd hk hkd, by
    -- Upper bound from OQ-02 (Erdős-style: 1-x ≤ exp(-x))
    unfold birthdayProduct
    calc ∏ i ∈ Finset.range k, (1 - (i : ℝ) / d)
        ≤ ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / d) := by
          apply Finset.prod_le_prod
            (fun i hi => birthdayProduct_factor_nonneg (by omega) hkd' i hi)
          intro i _
          have h := add_one_le_exp (-↑i / (↑d : ℝ))
          have : -↑i / (↑d : ℝ) + 1 = 1 - ↑i / ↑d := by ring
          linarith
      _ = Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d)) := by
          rw [Real.exp_sum]
      _ = Real.exp (-(↑k : ℝ) * (↑k - 1) / (2 * ↑d)) := by
          congr 1
          rw [show ∀ i : ℕ, -(↑i : ℝ) / ↑d = -(1 / ↑d) * ↑i from fun i => by ring]
          rw [← Finset.mul_sum]
          rw [show ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * (↑k - 1) / 2 from by
            have := Finset.sum_range_id_eq_sum_range_succ_div_two k
            push_cast at this ⊢
            linarith]
          ring
  ⟩
