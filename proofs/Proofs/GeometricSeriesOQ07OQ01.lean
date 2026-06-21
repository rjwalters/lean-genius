/-
# The General Moment of the Geometric Series

For `|r| < 1` and any order `m`, the `m`-th moment of the geometric weights `rⁿ` has the
closed form

  ∑_{n≥0} nᵐ · rⁿ  =  ∑_{k=0}^{m}  S(m,k) · k! · rᵏ / (1 - r)^{k+1},

where `S(m,k)` is the Stirling number of the second kind (`Nat.stirlingSecond`).

This answers the first open question of the gallery entry
`geometric-series-oq-07` ("The Second Moment of the Geometric Series"), which asked to
generalise the moment computation to arbitrary order with a polynomial-in-`r` numerator and
a `(1-r)^{m+1}` denominator. The Stirling-number formulation makes the change-of-basis
coefficients explicit and uniform in `m`: it recovers the gallery's order-0, order-1,
order-2 and order-3 formulas (`oq-07`, `oq-10`) as the special cases `m = 0,1,2,3`.

## Method

The proof rests on two ingredients.

* **The falling-factorial change of basis.** Every monomial expands over the falling
  factorials `n^{\underline k} = n.descFactorial k` with Stirling coefficients:
      nᵐ = ∑_{k=0}^{m} S(m,k) · n^{\underline k}.
  We prove this purely combinatorial `ℕ`-identity by induction on `m`, using the Stirling
  recurrence `S(m+1,k+1) = (k+1)·S(m,k+1) + S(m,k)` and the falling-factorial recurrence
  `n · n^{\underline k} = n^{\underline{k+1}} + k · n^{\underline k}`.

* **The falling-factorial geometric sum.** Mathlib already evaluates the *ascending*
  factorial generating function (`hasSum_choose_mul_geometric_of_norm_lt_one`). Shifting the
  index by `k` turns it into the falling-factorial sum
      ∑_{n≥0} n^{\underline k} · rⁿ = k! · rᵏ / (1 - r)^{k+1}.

Summing the (finite) Stirling expansion against `rⁿ` and using linearity of `HasSum` over the
finite range `0 ≤ k ≤ m` assembles the closed form.

All results are over `ℝ`; everything is `0`-axiom (`propext`/`Classical.choice`/`Quot.sound`
only) and `sorry`-free.
-/
import Mathlib

namespace GeometricSeriesOQ07OQ01

open Finset Nat

/-! ## Part 1: the falling-factorial change of basis (a combinatorial `ℕ`-identity) -/

/-- The falling-factorial recurrence in additive form, valid for all `n k : ℕ`
(no side condition `k ≤ n`):
`n · n^{\underline k} = n^{\underline{k+1}} + k · n^{\underline k}`. -/
theorem mul_descFactorial (n k : ℕ) :
    n * n.descFactorial k = n.descFactorial (k + 1) + k * n.descFactorial k := by
  rw [Nat.descFactorial_succ, ← add_mul]
  rcases le_or_gt k n with h | h
  · rw [Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

/-- **Stirling's monomial expansion.** Every power expands over the falling factorials with
Stirling-number-of-the-second-kind coefficients:
`n ^ m = ∑_{k=0}^{m} S(m,k) · n^{\underline k}`. -/
theorem pow_eq_sum_stirlingSecond_descFactorial (n m : ℕ) :
    n ^ m = ∑ k ∈ range (m + 1), stirlingSecond m k * n.descFactorial k := by
  induction m with
  | zero => simp [stirlingSecond_zero]
  | succ m ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    -- Rewrite each LHS summand `n · (S(m,k) · descFac n k)` using the falling-factorial
    -- recurrence, giving `S(m,k)·descFac n (k+1) + k·S(m,k)·descFac n k`.
    have hL : ∀ k ∈ range (m + 1),
        n * (stirlingSecond m k * n.descFactorial k)
          = stirlingSecond m k * n.descFactorial (k + 1)
            + k * stirlingSecond m k * n.descFactorial k := by
      intro k _
      rw [show n * (stirlingSecond m k * n.descFactorial k)
            = stirlingSecond m k * (n * n.descFactorial k) by ring, mul_descFactorial]
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib]
    -- LHS = S1 + S2, with
    --   S1 = ∑_{k<m+1} S(m,k) · descFac n (k+1)
    --   S2 = ∑_{k<m+1} k · S(m,k) · descFac n k
    -- Expand the RHS sum: peel the `k = 0` term (which vanishes) and apply the Stirling
    -- recurrence to the shifted summands.
    rw [Finset.sum_range_succ' (fun k => stirlingSecond (m + 1) k * n.descFactorial k) (m + 1)]
    have h0 : stirlingSecond (m + 1) 0 = 0 := stirlingSecond_succ_zero m
    rw [h0, zero_mul, add_zero]
    have hR : ∀ k ∈ range (m + 1),
        stirlingSecond (m + 1) (k + 1) * n.descFactorial (k + 1)
          = (k + 1) * stirlingSecond m (k + 1) * n.descFactorial (k + 1)
            + stirlingSecond m k * n.descFactorial (k + 1) := by
      intro k _
      rw [stirlingSecond_succ_succ]; ring
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib]
    -- RHS = T1 + S1, with T1 = ∑_{k<m+1} (k+1)·S(m,k+1)·descFac n (k+1).
    -- Goal is now `S1 + S2 = T1 + S1`; it suffices to prove `S2 = T1`.
    have hS2T1 : (∑ k ∈ range (m + 1), k * stirlingSecond m k * n.descFactorial k)
        = ∑ k ∈ range (m + 1),
            (k + 1) * stirlingSecond m (k + 1) * n.descFactorial (k + 1) := by
      rw [Finset.sum_range_succ' (fun k => k * stirlingSecond m k * n.descFactorial k) m,
          Finset.sum_range_succ
            (fun k => (k + 1) * stirlingSecond m (k + 1) * n.descFactorial (k + 1)) m]
      have hT : stirlingSecond m (m + 1) = 0 := stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m)
      rw [hT]
      simp
    omega

/-! ## Part 2: the falling-factorial geometric sum -/

/-- **Ascending-factorial geometric sum** (a thin wrapper over Mathlib's
`hasSum_choose_mul_geometric_of_norm_lt_one`, rephrased via
`descFactorial_eq_factorial_mul_choose`):
`∑_{n≥0} (n+k)^{\underline k} · rⁿ = k! / (1 - r)^{k+1}`. -/
theorem hasSum_ascFactorial_geometric (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n => ((n + k).descFactorial k : ℝ) * r ^ n)
      ((k.factorial : ℝ) / (1 - r) ^ (k + 1)) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hnorm).mul_left (k.factorial : ℝ)
  have hval : (k.factorial : ℝ) * (1 / (1 - r) ^ (k + 1)) = (k.factorial : ℝ) / (1 - r) ^ (k + 1) := by
    ring
  rw [hval] at h
  have hfun : (fun n => ((n + k).descFactorial k : ℝ) * r ^ n)
            = (fun n => (k.factorial : ℝ) * (((n + k).choose k : ℝ) * r ^ n)) := by
    funext n
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hfun]
  exact h

/-- **Falling-factorial geometric sum.** Shifting the ascending-factorial sum down by `k`
positions (the first `k` terms vanish since `n^{\underline k} = 0` for `n < k`):
`∑_{n≥0} n^{\underline k} · rⁿ = k! · rᵏ / (1 - r)^{k+1}`. -/
theorem hasSum_descFactorial_geometric (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n => (n.descFactorial k : ℝ) * r ^ n)
      ((k.factorial : ℝ) * r ^ k / (1 - r) ^ (k + 1)) := by
  have h := (hasSum_ascFactorial_geometric k hr).mul_left (r ^ k)
  have hval : r ^ k * ((k.factorial : ℝ) / (1 - r) ^ (k + 1))
            = (k.factorial : ℝ) * r ^ k / (1 - r) ^ (k + 1) := by ring
  rw [hval] at h
  -- Recognise `h` as the shifted version of the target sum.
  have hshift : HasSum (fun n => ((n + k).descFactorial k : ℝ) * r ^ (n + k))
      ((k.factorial : ℝ) * r ^ k / (1 - r) ^ (k + 1)) := by
    have hfun : (fun n => ((n + k).descFactorial k : ℝ) * r ^ (n + k))
              = (fun n => r ^ k * (((n + k).descFactorial k : ℝ) * r ^ n)) := by
      funext n; rw [pow_add]; ring
    rw [hfun]; exact h
  -- The first `k` terms of the un-shifted sum vanish.
  have hsum0 : ∑ i ∈ range k, ((i.descFactorial k : ℝ) * r ^ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hi]
    simp
  have key := (hasSum_nat_add_iff (f := fun n => (n.descFactorial k : ℝ) * r ^ n) k).mp hshift
  simp only [hsum0, add_zero] at key
  exact key

/-! ## Part 3: the general moment closed form -/

/-- **The general moment of the geometric series.** For `|r| < 1` and any order `m`,
`∑_{n≥0} nᵐ · rⁿ = ∑_{k=0}^{m} S(m,k) · k! · rᵏ / (1 - r)^{k+1}`. -/
theorem hasSum_pow_mul_geometric (m : ℕ) {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ m * r ^ n)
      (∑ k ∈ range (m + 1),
        (stirlingSecond m k : ℝ) * k.factorial * r ^ k / (1 - r) ^ (k + 1)) := by
  -- Cast the combinatorial Stirling expansion to `ℝ`.
  have hcast : ∀ n : ℕ, (n : ℝ) ^ m
      = ∑ k ∈ range (m + 1), (stirlingSecond m k : ℝ) * (n.descFactorial k : ℝ) := by
    intro n
    exact_mod_cast pow_eq_sum_stirlingSecond_descFactorial n m
  -- Each `k`-summand is a `HasSum` via the falling-factorial geometric sum.
  have hterm : ∀ k ∈ range (m + 1),
      HasSum (fun n => (stirlingSecond m k : ℝ) * ((n.descFactorial k : ℝ) * r ^ n))
        ((stirlingSecond m k : ℝ) * k.factorial * r ^ k / (1 - r) ^ (k + 1)) := by
    intro k _
    have h := (hasSum_descFactorial_geometric k hr).mul_left (stirlingSecond m k : ℝ)
    have hval : (stirlingSecond m k : ℝ) * ((k.factorial : ℝ) * r ^ k / (1 - r) ^ (k + 1))
              = (stirlingSecond m k : ℝ) * k.factorial * r ^ k / (1 - r) ^ (k + 1) := by ring
    rwa [hval] at h
  have hbig := hasSum_sum hterm
  -- Collapse the inner finite sum back to `nᵐ · rⁿ`.
  have hfun : (fun n : ℕ => ∑ k ∈ range (m + 1),
        (stirlingSecond m k : ℝ) * ((n.descFactorial k : ℝ) * r ^ n))
      = fun n : ℕ => (n : ℝ) ^ m * r ^ n := by
    funext n
    rw [hcast n, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hfun] at hbig
  exact hbig

/-- `tsum` form of the general moment closed form. -/
theorem tsum_pow_mul_geometric (m : ℕ) {r : ℝ} (hr : |r| < 1) :
    ∑' n : ℕ, (n : ℝ) ^ m * r ^ n
      = ∑ k ∈ range (m + 1),
          (stirlingSecond m k : ℝ) * k.factorial * r ^ k / (1 - r) ^ (k + 1) :=
  (hasSum_pow_mul_geometric m hr).tsum_eq

/-! ## Part 4: recovering the gallery's low-order moments

The general formula specialises to the moments already in the gallery.  The Stirling
coefficients are evaluated by `decide`; the resulting `r`-rational identities by `ring`
(after clearing the nonzero denominator `(1 - r) ≠ 0`). -/

/-- Order 0 (the geometric series itself): `∑ rⁿ = 1/(1-r)`. -/
example {r : ℝ} (hr : |r| < 1) : ∑' n : ℕ, (n : ℝ) ^ 0 * r ^ n = 1 / (1 - r) := by
  rw [tsum_pow_mul_geometric 0 hr]
  simp [stirlingSecond_zero]

/-- Order 1: `∑ n·rⁿ = r/(1-r)²`. -/
example {r : ℝ} (hr : |r| < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 1 * r ^ n = r / (1 - r) ^ 2 := by
  have hne : (1 - r) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hr; simp at hr
  rw [tsum_pow_mul_geometric 1 hr]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [show stirlingSecond 1 0 = 0 from by decide, show stirlingSecond 1 1 = 1 from by decide]
  field_simp
  ring

/-- Order 2 (the gallery's `oq-07`): `∑ n²·rⁿ = r(1+r)/(1-r)³`. -/
example {r : ℝ} (hr : |r| < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hne : (1 - r) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hr; simp at hr
  rw [tsum_pow_mul_geometric 2 hr]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show stirlingSecond 2 0 = 0 from by decide, show stirlingSecond 2 1 = 1 from by decide,
      show stirlingSecond 2 2 = 1 from by decide]
  field_simp
  ring

/-- Order 3 (the gallery's `oq-10`): `∑ n³·rⁿ = r(1+4r+r²)/(1-r)⁴`. -/
example {r : ℝ} (hr : |r| < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 3 * r ^ n = r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 := by
  have hne : (1 - r) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hr; simp at hr
  rw [tsum_pow_mul_geometric 3 hr]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show stirlingSecond 3 0 = 0 from by decide, show stirlingSecond 3 1 = 1 from by decide,
      show stirlingSecond 3 2 = 3 from by decide, show stirlingSecond 3 3 = 1 from by decide]
  field_simp
  ring

end GeometricSeriesOQ07OQ01
