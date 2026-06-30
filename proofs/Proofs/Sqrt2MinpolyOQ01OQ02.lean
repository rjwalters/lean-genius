import Mathlib

open Polynomial IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √r over ℚ for a Rational Radicand r

**Open Question (from sqrt2-minpoly-oq-01-oq-02)**:

The gallery already proves `minpoly ℚ (√n) = X² - n` for every non-perfect-square
natural number `n` (see `Sqrt2MinpolyOQ01.minpoly_sqrt_of_not_sq`). This file
generalizes the radicand from a natural number to an arbitrary **nonnegative rational**
`r`:

  if `r ≥ 0` is not a square in `ℚ`, then `minpoly ℚ (√r) = X² - r`.

Equivalently, writing `r = p/q` in lowest terms, the (monic) minimal polynomial is
`X² - p/q`, whose cleared-denominator associate is `q·X² - p`.

## Mathematical Content

The minimal polynomial is, by definition, **monic**, so the canonical answer is the
monic `X² - C r`; the form `q·X² - p` from the problem statement is the non-monic
integer associate obtained by scaling by `C q` (see `cleared_denom_form`).

The proof mirrors the natural-number argument of `Sqrt2MinpolyOQ01` Part VII:
1. `X² - C r` is monic and has `√r` as a root, so `minpoly ℚ (√r) ∣ X² - C r`,
   giving degree `≤ 2`.
2. If `r` is not a rational square then `√r` is irrational, forcing degree `≥ 2`.
3. A monic divisor of a monic degree-2 polynomial that itself has degree 2 must equal it.

The irrationality step is in fact **simpler** over `ℚ` than over `ℕ`: if `√r = (s : ℝ)`
for some rational `s`, then `s² = r` exhibits `r` as a rational square directly — no
appeal to `irrational_nrt_of_notint_nrt` is needed.

## Corollary

`√r` is irrational **iff** `r` is not a rational square (for `r ≥ 0`).

## Status: 0 sorries, 0 axioms. Build-pending (Docker/Aristotle unavailable this session);
proof is a direct adaptation of the machine-verified `Sqrt2MinpolyOQ01` Part VII.
-/

namespace Sqrt2MinpolyOQ01OQ02

/-! ## Part I: Irrationality for a Rational Radicand -/

/-- If `r` is a nonnegative rational that is **not** a square in `ℚ`, then `√r` is
    irrational.

    Direct proof: a rational value `s` of `√r` would satisfy `s² = r`, making `r` a
    rational square. -/
theorem irrational_sqrt_of_not_isSquare_rat (r : ℚ) (hr : 0 ≤ r) (hns : ¬ IsSquare r) :
    Irrational (Real.sqrt (r : ℝ)) := by
  rintro ⟨s, hs⟩
  apply hns
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hsq : (s : ℝ) ^ 2 = (r : ℝ) := by rw [hs]; exact Real.sq_sqrt hr'
  have hsq_q : s ^ 2 = r := by exact_mod_cast hsq
  exact ⟨s, by rw [← hsq_q]; ring⟩

/-! ## Part II: The Minimal Polynomial -/

/-- **Main Theorem**: `minpoly ℚ (√r) = X² - r` for any nonnegative rational `r`
    that is not a square in `ℚ`.

    This generalizes `Sqrt2MinpolyOQ01.minpoly_sqrt_of_not_sq` from natural-number
    radicands to rational radicands. -/
theorem minpoly_sqrt_of_not_isSquare_rat (r : ℚ) (hr : 0 ≤ r) (hns : ¬ IsSquare r) :
    minpoly ℚ (Real.sqrt (r : ℝ)) = X ^ 2 - C r := by
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hAM : (algebraMap ℚ ℝ) r = (r : ℝ) := eq_ratCast (algebraMap ℚ ℝ) r
  have hXn_monic : (X ^ 2 - C r : ℚ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hXn_aeval : Polynomial.aeval (Real.sqrt (r : ℝ)) (X ^ 2 - C r : ℚ[X]) = 0 := by
    have hsq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt hr'
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hAM, hsq, sub_self]
  have hintegral : IsIntegral ℚ (Real.sqrt (r : ℝ)) :=
    ⟨X ^ 2 - C r, hXn_monic, hXn_aeval⟩
  have hdvd : minpoly ℚ (Real.sqrt (r : ℝ)) ∣ X ^ 2 - C r :=
    minpoly.dvd ℚ (Real.sqrt (r : ℝ)) hXn_aeval
  have hXn_ne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.Monic.ne_zero hXn_monic
  have hdeg_le : (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hXn_ne
    simpa [Polynomial.natDegree_X_pow_sub_C] using this
  have hirr : Irrational (Real.sqrt (r : ℝ)) :=
    irrational_sqrt_of_not_isSquare_rat r hr hns
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
    rw [eq_ratCast (algebraMap ℚ ℝ) b] at heval
    exact hirr ⟨-b, by push_cast; linarith⟩
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

/-! ## Part III: Irrationality Characterization -/

/-- **Corollary**: For `r ≥ 0`, `√r` is irrational **iff** `r` is not a rational square. -/
theorem irrational_sqrt_iff_not_isSquare_rat (r : ℚ) (hr : 0 ≤ r) :
    Irrational (Real.sqrt (r : ℝ)) ↔ ¬ IsSquare r := by
  constructor
  · rintro hirr ⟨s, hs⟩
    -- r = s*s is a rational square, so √r = |s| is rational, contradicting irrationality.
    apply hirr
    refine ⟨|s|, ?_⟩
    have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrs : (r : ℝ) = (|s| : ℝ) ^ 2 := by
      have : (r : ℝ) = (s : ℝ) * (s : ℝ) := by rw [hs]; push_cast; ring
      rw [this]; push_cast; rw [sq_abs]; ring
    rw [hrs, Real.sqrt_sq (by positivity)]
  · exact irrational_sqrt_of_not_isSquare_rat r hr

/-! ## Part IV: Degree and Field-Extension Consequences -/

/-- The algebraic degree of `√r` over `ℚ` is `2`, for `r ≥ 0` not a rational square. -/
theorem minpoly_sqrt_natDegree (r : ℚ) (hr : 0 ≤ r) (hns : ¬ IsSquare r) :
    (minpoly ℚ (Real.sqrt (r : ℝ))).natDegree = 2 := by
  rw [minpoly_sqrt_of_not_isSquare_rat r hr hns, Polynomial.natDegree_X_pow_sub_C]

/-- `√r` is integral over `ℚ` for `r ≥ 0`. -/
theorem sqrt_isIntegral (r : ℚ) (hr : 0 ≤ r) : IsIntegral ℚ (Real.sqrt (r : ℝ)) := by
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  refine ⟨X ^ 2 - C r, monic_X_pow_sub_C _ (by norm_num), ?_⟩
  have hAM : (algebraMap ℚ ℝ) r = (r : ℝ) := eq_ratCast (algebraMap ℚ ℝ) r
  have hsq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt hr'
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [hAM, hsq, sub_self]

/-- **Field Extension Degree**: `[ℚ(√r) : ℚ] = 2` for `r ≥ 0` not a rational square. -/
theorem adjoin_sqrt_finrank (r : ℚ) (hr : 0 ≤ r) (hns : ¬ IsSquare r) :
    Module.finrank ℚ ℚ⟮Real.sqrt (r : ℝ)⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (sqrt_isIntegral r hr)]
  exact minpoly_sqrt_natDegree r hr hns

/-! ## Part V: Explicit `p/q` and Cleared-Denominator Forms -/

/-- Pure polynomial identity relating the monic minimal polynomial `X² - p/q` to its
    cleared-denominator integer associate `q·X² - p`. -/
theorem cleared_denom_form (p q : ℚ) (hq : q ≠ 0) :
    C q * (X ^ 2 - C (p / q)) = C q * X ^ 2 - C p := by
  have hpq : q * (p / q) = p := by field_simp
  rw [mul_sub, ← C_mul, hpq]

/-- **Explicit `p/q` form**: for naturals `p`, `q` with `q > 0` such that `p/q` is not a
    rational square, `minpoly ℚ (√(p/q)) = X² - p/q`. -/
theorem minpoly_sqrt_div (p q : ℕ) (hq : 0 < q) (hns : ¬ IsSquare ((p : ℚ) / q)) :
    minpoly ℚ (Real.sqrt ((p : ℝ) / q)) = X ^ 2 - C ((p : ℚ) / q) := by
  have hr : (0 : ℚ) ≤ (p : ℚ) / q := by positivity
  have key := minpoly_sqrt_of_not_isSquare_rat ((p : ℚ) / q) hr hns
  have hcast : (((p : ℚ) / q : ℚ) : ℝ) = (p : ℝ) / (q : ℝ) := by push_cast; ring
  rwa [hcast] at key

/-! ## Part VI: Concrete Examples -/

/-- `2` is not a square in `ℚ`, recovered from the irrationality of `√2`. -/
private lemma not_isSquare_two : ¬ IsSquare (2 : ℚ) := by
  have h : Irrational (Real.sqrt ((2 : ℚ) : ℝ)) := by
    rw [show ((2 : ℚ) : ℝ) = (2 : ℝ) from by norm_num]
    exact irrational_sqrt_two
  exact (irrational_sqrt_iff_not_isSquare_rat 2 (by norm_num)).mp h

/-- `1/2` is not a square in `ℚ` (a square iff its inverse `2` is a square). -/
private lemma not_isSquare_half : ¬ IsSquare ((1 : ℚ) / 2) := by
  rw [one_div, isSquare_inv]
  exact not_isSquare_two

/-- **Genuinely rational radicand**: `minpoly ℚ (√(1/2)) = X² - 1/2`.
    Here `√(1/2) = √2 / 2` is irrational and `1/2` is not an integer. -/
theorem minpoly_sqrt_half : minpoly ℚ (Real.sqrt ((1 : ℝ) / 2)) = X ^ 2 - C (1 / 2) := by
  have hns : ¬ IsSquare (((1 : ℕ) : ℚ) / ((2 : ℕ) : ℚ)) := by
    simpa using not_isSquare_half
  have := minpoly_sqrt_div 1 2 (by norm_num) hns
  simpa using this

end Sqrt2MinpolyOQ01OQ02
