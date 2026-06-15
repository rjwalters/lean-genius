import Mathlib

open Polynomial

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √(p/q) over ℚ

**Open Question (from sqrt2-minpoly-oq-01)**:

The parent result `sqrt2-minpoly-oq-01` proves `minpoly ℚ (√n) = X² - n` for every
non-perfect-square natural number `n`. This file generalizes that to the square root
of an arbitrary non-negative **rational** `r = p/q`:

    minpoly ℚ (√r) = X² - r        (monic form)

equivalently, multiplying through by the denominator `q`,

    q • minpoly ℚ (√(p/q)) = q X² - p   (integer form, `q > 0`)

provided `r` is not the square of a rational (otherwise `√r ∈ ℚ` and the degree drops
to 1). The irrationality corollary `√(p/q) irrational ↔ p/q not a rational square`
is recorded as `irrational_sqrt_rat_iff`.

## Strategy

This mirrors Part VII of `Sqrt2MinpolyOQ01.lean` (`minpoly_sqrt_of_not_sq`), with the
natural number `n` replaced by a rational `r`:

1. `X² - C r` is monic, degree 2, and has `√r` as a root ⟹ `minpoly ∣ X² - C r`, so
   `deg (minpoly) ≤ 2`.
2. `√r` irrational ⟹ `deg (minpoly) ≥ 2` (a degree-1 minimal polynomial would put
   `√r ∈ ℚ`).
3. Both monic of degree 2 with `minpoly ∣ X² - C r` ⟹ they are equal.

## Status: 0 axioms. Build-pending (Docker host saturated this session).
-/

namespace Sqrt2MinpolyOQ01OQ02

/-! ## Part I: Irrationality characterization for rational radicands -/

/-- If the non-negative rational `r` is not the square of a rational, then `√r` is
    irrational. (One direction of `irrational_sqrt_rat_iff`; the workhorse for the
    minimal-polynomial degree bound.) -/
theorem irrational_sqrt_rat_of_not_square (r : ℚ) (hr : 0 ≤ r)
    (hns : ¬ ∃ s : ℚ, s ^ 2 = r) : Irrational (Real.sqrt (r : ℝ)) := by
  intro h
  obtain ⟨a, ha⟩ := h
  apply hns
  refine ⟨a, ?_⟩
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (a : ℝ) ^ 2 = (r : ℝ) := by rw [ha]; exact Real.sq_sqrt hr'
  exact_mod_cast h2

/-- **Irrationality corollary**: for a non-negative rational `r`, `√r` is irrational
    iff `r` is not the square of a rational. -/
theorem irrational_sqrt_rat_iff (r : ℚ) (hr : 0 ≤ r) :
    Irrational (Real.sqrt (r : ℝ)) ↔ ¬ ∃ s : ℚ, s ^ 2 = r := by
  constructor
  · rintro hirr ⟨s, hs⟩
    apply hirr
    refine ⟨|s|, ?_⟩
    have hsr : ((s : ℝ)) ^ 2 = (r : ℝ) := by exact_mod_cast hs
    rw [show ((|s| : ℚ) : ℝ) = |(s : ℝ)| by norm_cast,
        ← Real.sqrt_sq_eq_abs, hsr]
  · exact irrational_sqrt_rat_of_not_square r hr

/-! ## Part II: Main theorem — `minpoly ℚ (√r) = X² - C r` -/

/-- **Main Result**: For a non-negative rational `r` whose square root is irrational,
    the minimal polynomial of `√r` over ℚ is the monic quadratic `X² - r`.

    This generalizes `minpoly ℚ (√n) = X² - n` from natural-number radicands
    (`Sqrt2MinpolyOQ01.minpoly_sqrt_of_not_sq`) to rational radicands. -/
theorem minpoly_sqrt_rat (r : ℚ) (hr : 0 ≤ r) (hirr : Irrational (Real.sqrt (r : ℝ))) :
    minpoly ℚ (Real.sqrt (r : ℝ)) = X ^ 2 - C r := by
  have hXn_monic : (X ^ 2 - C r : ℚ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hXn_aeval : Polynomial.aeval (Real.sqrt (r : ℝ)) (X ^ 2 - C r : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    push_cast
    linarith [Real.sq_sqrt (show (0 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr)]
  have hintegral : IsIntegral ℚ (Real.sqrt (r : ℝ)) :=
    ⟨X ^ 2 - C r, hXn_monic, hXn_aeval⟩
  have hdvd : minpoly ℚ (Real.sqrt (r : ℝ)) ∣ X ^ 2 - C r :=
    minpoly.dvd ℚ (Real.sqrt (r : ℝ)) hXn_aeval
  have hXn_ne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.Monic.ne_zero hXn_monic
  have hdeg_le : (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hXn_ne
    simpa [Polynomial.natDegree_X_pow_sub_C] using this
  have hdeg_ge : 2 ≤ (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hdeg1 : (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree = 1 := by
      have hge1 := minpoly.natDegree_pos hintegral; omega
    obtain ⟨a, b, ha, hfab⟩ := Polynomial.natDegree_eq_one.mp hdeg1
    have hmonic := minpoly.monic hintegral
    have ha1 : a = 1 := by
      have hlc := hmonic.leadingCoeff
      rw [hfab] at hlc
      simp [Polynomial.leadingCoeff_add_of_degree_lt, Polynomial.degree_C_mul_X ha,
            Polynomial.degree_C, ha] at hlc
      exact hlc
    rw [ha1, one_mul] at hfab
    have heval := minpoly.aeval ℚ (Real.sqrt (r : ℝ))
    rw [hfab] at heval
    simp only [map_add, aeval_X, aeval_C] at heval
    exact hirr ⟨-b, by push_cast at heval ⊢; linarith⟩
  have hdeg : (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree = 2 := Nat.le_antisymm hdeg_le hdeg_ge
  obtain ⟨c, hc⟩ := hdvd
  have hc_ne : c ≠ 0 := by intro hc0; simp [hc0] at hc; exact hXn_ne hc
  have hc_deg : c.natDegree = 0 := by
    have hmul_deg := Polynomial.natDegree_mul (minpoly.ne_zero hintegral) hc_ne
    rw [← hc, Polynomial.natDegree_X_pow_sub_C, hdeg] at hmul_deg
    omega
  have hc_one : c = 1 := by
    have hmul_lc : (minpoly ℚ (Real.sqrt (r : ℝ)) * c).leadingCoeff = 1 := by
      rw [← hc]; exact hXn_monic.leadingCoeff
    rw [Polynomial.leadingCoeff_mul, (minpoly.monic hintegral).leadingCoeff, one_mul] at hmul_lc
    have hc_const := Polynomial.eq_C_of_natDegree_eq_zero hc_deg
    rw [hc_const, Polynomial.leadingCoeff_C] at hmul_lc
    rw [hc_const, hmul_lc, map_one]
  rw [hc_one, mul_one] at hc
  exact hc.symm

/-- Convenience form taking the "not a rational square" hypothesis directly. -/
theorem minpoly_sqrt_rat_of_not_square (r : ℚ) (hr : 0 ≤ r)
    (hns : ¬ ∃ s : ℚ, s ^ 2 = r) :
    minpoly ℚ (Real.sqrt (r : ℝ)) = X ^ 2 - C r :=
  minpoly_sqrt_rat r hr (irrational_sqrt_rat_of_not_square r hr hns)

/-! ## Part III: Integer form `q X² - p` -/

/-- **Integer form**: scaling the monic minimal polynomial by the denominator `q`
    recovers the cleared-denominator quadratic `q X² - p`. Here `p q : ℤ`, `q > 0`,
    and `√(p/q)` is irrational. -/
theorem minpoly_sqrt_div_integer_form (p q : ℤ) (hq : 0 < q)
    (hr : (0 : ℚ) ≤ (p : ℚ) / (q : ℚ))
    (hirr : Irrational (Real.sqrt (((p : ℚ) / (q : ℚ) : ℚ) : ℝ))) :
    C (q : ℚ) * minpoly ℚ (Real.sqrt (((p : ℚ) / (q : ℚ) : ℚ) : ℝ))
      = C (q : ℚ) * X ^ 2 - C (p : ℚ) := by
  have hpq : (q : ℚ) * ((p : ℚ) / (q : ℚ)) = (p : ℚ) := by
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  rw [minpoly_sqrt_rat ((p : ℚ) / (q : ℚ)) hr hirr, mul_sub, ← C_mul, hpq]

/-! ## Part IV: Examples -/

/-- Sanity check: the rational theorem recovers the parent `minpoly ℚ (√2) = X² - 2`. -/
example : minpoly ℚ (Real.sqrt ((2 : ℚ) : ℝ)) = X ^ 2 - C (2 : ℚ) :=
  minpoly_sqrt_rat 2 (by norm_num)
    (by rw [show ((2 : ℚ) : ℝ) = (2 : ℝ) by norm_num]; exact Real.irrational_sqrt_two)

end Sqrt2MinpolyOQ01OQ02
